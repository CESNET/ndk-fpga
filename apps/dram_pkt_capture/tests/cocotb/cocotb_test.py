# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#            Daniel Kondys <kondys@cesnet.cz>
#            Adam Zatloukal <zatloukal@cesnet.cz>

import logging
import cocotb
import random
from collections import Counter
from cocotb.clock import Clock
from cocotb.handle import Force
from cocotb.triggers import Timer, Event
from cocotbext.ofm.base.bus_fixup import SignalProxy
from cocotbext.ofm.ver.generators import random_packets
from cocotbext.ofm.utils.hex_formatter import format_bytes


from cocotbext.ndk_core import NFBDevice
from cocotbext.nfb.queue import NDP_RX_CALYPTE_BLOCK_SIZE

import cocotbext.ofm.utils.sim.modelsim as ms
import cocotb.utils

from cocotbext.ofm.utils.sim.bus import MfbBus, MiBus, DmaUpMvbBus, DmaDownMvbBus

from dram_pkt_capture_regs import AppStatus


logger = logging.getLogger(__name__)
#logger.setLevel(logging.DEBUG)
#logging.getLogger("cocotbext.nfb.ext").setLevel(logging.DEBUG)
#logging.getLogger("cocotbext.ofm.pcie").setLevel(logging.DEBUG)


# Shortcuts
e = cocotb.task.bridge
st = cocotb.utils.get_sim_time


async def get_dev(dut, init=True, **kwargs):
    dev = NFBDevice(dut, **kwargs)
    if init:
        await dev.init()
    _init_mem_clk_rst(dut)
    return dev, dev.nfb


def _init_mem_clk_rst(dut):
    # Drive the memory clock and release the reset from the testbench.

    mem_clk_period = cocotb.utils.get_sim_steps(10/3 / 2, 'ns', round_mode='round') * 2
    mem_clk = SignalProxy(dut.mem_clk)
    for p in range(len(dut.mem_clk)):
        cocotb.start_soon(Clock(mem_clk[p], mem_clk_period, 'step').start())

    mem_rst_n = dut._get("mem_rst_n")
    if mem_rst_n is None:
        logger.warning(
            "Top-level signal 'mem_rst_n' not visible to cocotb; "
            "skipping reset override (memory reset is driven by the EMIF model)."
        )
        return
    mem_rst_n.value = Force((1 << len(mem_rst_n)) - 1)


@cocotb.test(timeout_time=200, timeout_unit='us', skip=True)
async def test_ndp_recvmsg(dut):
    dev, nfb = await get_dev(dut)

    for eth in nfb.eth:
        await e(eth.rxmac.enable)()

    await e(nfb.ndp.rx[0].start)()
    await dev.dma.rx[0]._push_desc()
    await Timer(2, unit='us')

    #pkt = bytes(raw(Ether()/IP(dst="127.0.0.1")/TCP()/"GET /index.html HTTP/1.0 \n\n"))
    pkt = bytes([i for i in range(72)])

    dev._eth_rx_driver[0].append(pkt)
    await Timer(105, unit='us')

    recv = await e(nfb.ndp.rx[0].recv)()

    # FIXME: try again for slower cards
    #if [pkt] != recv:
    #    await Timer(85, unit='us')
    #    recv = await e(nfb.ndp.rx[0].recv)()

    assert [pkt] == recv


@cocotb.test()
async def test_ndp_rcv_msg_multi(dut, frame_count=20000, frame_size_min=64, frame_size_max=512):
    """ This test keeps sending packets until the FULL flag is asserted on ANY core,
        afterwards it waits for DRAM to drain and checks if the RECEIVED data is a
        SUBSET of sent data.

        DMA BUFFERS MUST BE LARGE ENOUGH:
            -> in queue.py  _buffer_size = 4MB
            -> in device.py ram size = 0x10000000 (256 MB)

        Only uses SUBCORE 0
    """

    async def receive_all():
        full_seen = False
        idle_cycles = 0
        recv_cnt = 0
        while True:
            got_any = False
            for ch in range(len(nfb.ndp.rx)):
                # Poll DMA channel
                pkts = await e(nfb.ndp.rx[ch].recv)()

                if pkts:
                    got_any = True
                received.extend(pkts)

                for pkt in pkts:
                    recv_cnt += 1
                    cocotb.log.info(f"RX[ch={ch}][{len(received)}]: len={len(pkt)} data={pkt.hex()}")

            # Check FULL register
            if full_event.is_set():
                full_seen = True

            # If FULL was asserted and no new packets were drained EXIT
            if full_seen and not got_any:
                idle_cycles += 1
                if idle_cycles % 25 == 0:
                    cocotb.log.info(f"Zero TX throughput event detected, idle cycles: {idle_cycles}")
                if idle_cycles >= 10000:
                    break
            else:
                idle_cycles = 0

            # Check if all packets were received
            if recv_cnt == frame_count:
                cocotb.log.info("Received every expected packet")
                break

            await Timer(5, unit='ns')

    # Log dropped frames
    async def log_rxmac_stats():
        while not stop_stats.is_set():
            stats = await e(nfb.eth[0].rxmac.read_stats)()
            cocotb.log.info(f"RXMAC dropped: {stats['dropped']}\noverflowed: {stats['overflowed']}")
            await Timer(10, unit='us')

    async def log_dram_full():
        while not stop_status.is_set():
            for i, st in enumerate(app_status):
                en = await e(lambda: st.capture_enable)()
                if not en:                    # was enabled at start, now cleared => full fired
                    full_event.set()
                    await e(st.set_read_enable)(True)
                cocotb.log.info(f"APP_STATUS[{i}]: capture_enable={int(en)}")
            await Timer(1, unit='us')

    dev, nfb = await get_dev(dut)

    q0 = dev.dma.rx[0]
    rx_chans = len(dev.dma.rx)
    cap_blocks = q0._desc_cnt * rx_chans
    cocotb.log.info(
        f"DMA host buffers: _buffer_size={q0._buffer_size} B ({q0._buffer_size // 1024} KiB), "
        f"_packet_length_max={q0._packet_length_max} B, "
        f"block={NDP_RX_CALYPTE_BLOCK_SIZE} B, "
        f"blocks/channel={q0._desc_cnt}, rx_channels={rx_chans}, "
        f"capacity={cap_blocks} blocks ({cap_blocks * NDP_RX_CALYPTE_BLOCK_SIZE // 1024} KiB)"
    )

    expected = []
    received = []

    # Set enable bit in each eth ports CSR register (RX MAC lite component)
    # By default each frame that arrives would otherwise be discarded
    for eth in nfb.eth:
        await e(eth.rxmac.enable)()

    # For each dma channel allocate resources in dev.ram
    # push dma desciptors into dev.ram (descriptor ring), increment SDP
    # save new SDP into a register inside the DMA engine
    for ch in range(len(nfb.ndp.rx)):
        await e(nfb.ndp.rx[ch].start)()

        # mdp is only valid once the queue is started
        cocotb.log.info(f"DMA rx[{ch}]: mdp={dev.dma.rx[ch]._ctrl.mdp}")

        # Almost fill the descriptor ring
        for _ in range(dev.dma.rx[ch]._ctrl.mdp - 2):
            await dev.dma.rx[ch]._push_desc(flush=False)
        await e(dev.dma.rx[ch]._ctrl.flush_sp)()

    await Timer(500, unit='ns')

    full_event = Event()

    recv_task = cocotb.start_soon(receive_all())

    stop_stats = Event()
    stop_status = Event()
    stats_task = cocotb.start_soon(log_rxmac_stats())
    app_status = [AppStatus(dev=nfb, index=i) for i in range(ETH_STREAMS)]

    await Timer(1, unit='us')

    for i, st in enumerate(app_status):
        await e(st.set_capture_enable)(True)
        await e(st.set_read_enable)(False)
        enabled = await e(lambda: st.capture_enable)()
        read_en = await e(lambda: st.read_enable)()
        cocotb.log.info(f"subcore[{i}] - ENABLE: {enabled} \t READ_EN: {read_en} ")

    status_task = cocotb.start_soon(log_dram_full())

    # insert packets into the dut
    sent = 0
    for i, pkt in enumerate(random_packets(frame_size_min, frame_size_max, frame_count)):
        # Stop sending packets when FULL
        if full_event.is_set():
            cocotb.log.info(f"dram_full asserted after {sent} packets, stopping TX")
            break

        # Drive the packet into DUT
        cocotb.log.info(f"TX[{i}]: len={len(pkt)} data={pkt.hex()}")
        expected.append(pkt)
        dev._eth_rx_driver[0].append(pkt)
        sent += 1

        await Timer(random.randint(50, 150), unit='ns')

    await recv_task

    stop_stats.set()
    stop_status.set()
    await stats_task
    await status_task

    for i, st in enumerate(app_status):
        enabled = await e(lambda: st.capture_enable)()
        cocotb.log.info(f"subcore[{i}] - ENABLE: {enabled} ")

    cocotb.log.info("=========================================================")

    for i, got in enumerate(received):
        exp = expected[i] if i < len(expected) else None
        assert i < len(expected) and got == exp, (
            f"Mismatch at packet [{i}]:\n"
            + (format_bytes(exp, label=f"expected[{i}]") if exp is not None else f"  expected[{i}]: <none — extra packet>\n")
            + "\n"
            + format_bytes(got, label=f"received[{i}]")
        )

    # At end of test:
    sent_cnt = Counter(expected)
    recv_cnt = Counter(received)

    # No packet received more times than it was sent (catches duplication)
    duplicates = recv_cnt - sent_cnt
    assert not duplicates, f"Duplicated/corrupted packets: {list(duplicates.items())[:5]}"

    # Every received packet is a sent packet
    assert all(pkt in sent_cnt for pkt in received), "Received a packet never sent"

    cocotb.log.info(f"Sent {len(expected)}, received {len(received)}, "
                    f"unique sent {len(sent_cnt)}, matched {sum((recv_cnt & sent_cnt).values())}")


core = NFBDevice.core_instance_from_top(cocotb.top)

pcic = core.pcie_i.pcie_core_i
ms.cmd(f"log -recursive {ms.cocotb2path(core)}/*")
ms.cmd(f"log -recursive {ms.cocotb2path(core)}/pcie_i/*")
ms.cmd(f"log -recursive {ms.cocotb2path(core)}/dma_i/dma_i/*")
ms.cmd(f"log -recursive {ms.cocotb2path(core)}/app_i/*")
ms.cmd(f"log -recursive {ms.cocotb2path(core)}/network_mod_i/*")
ms.cmd(f"log {ms.cocotb2path(core)}/dma_i/*")

DMA_STREAMS = core.dma_i.DMA_STREAMS.value
DMA_ENDPOINTS = core.dma_i.DMA_ENDPOINTS.value
ETH_STREAMS = core.app_i.ETH_STREAMS.value

ms.add_wave(core.pcie_i.MI_RESET)
ms.add_wave(core.pcie_i.MI_CLK)
MiBus(core.pcie_i, 'MI', 0, label='MI_PCIe').add_wave()
MiBus(core.app_i, 'MI', label='MI_APP').add_wave()

ms.add_wave(core.dma_i.USR_CLK)
for i in range(DMA_STREAMS):
    MfbBus(core.dma_i, "RX_USR_MFB", i).add_wave(groups=["DMA_RX_MFB", i], expand=[1])
    MfbBus(core.dma_i, "TX_USR_MFB", i).add_wave(groups=["DMA_TX_MFB", i], expand=[1])
    MfbBus(core.app_i, "DMA_RX_MFB", i, slices=DMA_STREAMS).add_wave(groups=["APP_DMA_RX_MFB", i], expand=[1])
    MfbBus(core.app_i, "DMA_TX_MFB", i, slices=DMA_STREAMS).add_wave(groups=["APP_DMA_TX_MFB", i], expand=[1])

for i in range(DMA_ENDPOINTS):
    DmaUpMvbBus(core.dma_i, 'PCIE_RQ_MVB', i).add_wave(groups=["DMA2PCIe", "RQ MVB", i], expand=[2, 3])
    MfbBus(core.dma_i, 'PCIE_RQ_MFB', i).add_wave(groups=["DMA2PCIe", "RQ MFB", i], expand=[2])
    DmaDownMvbBus(core.dma_i, 'PCIE_RC_MVB', i).add_wave(groups=["DMA2PCIe", "RC MVB", i], expand=[2, 3])
    MfbBus(core.dma_i, 'PCIE_RQ_MFB', i).add_wave(groups=["DMA2PCIe", "RC MFB", i], expand=[2])

clk_eth = SignalProxy(core.app_i.CLK_ETH, 0)
ms.add_wave(clk_eth)
for i in range(ETH_STREAMS):
    MfbBus(core.app_i, 'ETH_RX_MFB', i, label=f"ETH_RX_MFB{i}").add_wave()
    MfbBus(core.app_i, 'ETH_TX_MFB', i, label=f"ETH_TX_MFB{i}").add_wave()
