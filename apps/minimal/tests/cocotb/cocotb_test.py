# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#            Daniel Kondys <kondys@cesnet.cz>

import logging
from cocotbext.ofm.utils import partial
import cocotb
from cocotb.triggers import Timer

from cocotbext.ndk_core import NFBDevice

import cocotbext.ofm.utils.sim.modelsim as ms
import cocotb.utils

from cocotbext.ofm.utils.sim.bus import MfbBus, MiBus, DmaUpMvbBus, DmaDownMvbBus

from ofm.comp.base.misc.frequency_meter import FrequencyMeter, tabulate_data

from cocotbext.ofm.base.bus_fixup import SignalProxy


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
    return dev, dev.nfb


@cocotb.test(timeout_time=200, timeout_unit='us', skip=False)
async def test_mi_access_unaligned(dut):
    dev, nfb = await get_dev(dut)
    c = nfb.comp_open("cesnet,ofm,mi_test_space")
    await e(c.read)(0, 1)

    #for i in range(46, 64): # FIXME: Test fails (for US+)
    for i in range(24, 42):
        for x in range(0, 5):
            data = bytes([(j % 256) for j in range(i)])
            await e(c.write)(x, data)
            rdata = await e(c.read)(x, len(data))

            assert data == rdata, f"{list(data)}, {list(rdata)}"


@cocotb.test(timeout_time=50, timeout_unit='us', skip=False)
async def test_enable_rxmac_and_check_status(dut):
    dev, nfb = await get_dev(dut)

    mac = nfb.eth[0].rxmac
    await e(mac.enable)()
    await e(mac.is_enabled)()
    await e(nfb.ndp.rx[0].read_stats)()


@cocotb.test(timeout_time=100, timeout_unit='us', skip=False)
async def test_frequency_meter(dut):
    dev, nfb = await get_dev(dut)
    fm = await e(FrequencyMeter)(dev=nfb)

    def make_a_measurement():
        fm.interval = 1000
        data = fm.measure()
        table = tabulate_data(data)
        assert table is not None
        # print(table)

    await e(make_a_measurement)()


@cocotb.test(timeout_time=200, timeout_unit='us', skip=False)
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


#FIXME: test doesn't shuts DMA
#@cocotb.test(timeout_time=200, timeout_unit='us')
#async def test_ndp_recvmsg2(dut):
#    await test_ndp_recvmsg(dut)


async def _test_ndp_sendmsg(dut, dev=None, nfb=None):
    if dev is None:
        dev, nfb = await get_dev(dut)

    for eth in nfb.eth:
        await e(eth.txmac.reset_stats)()
        await e(eth.txmac.enable)()

    for i, tx in enumerate(dev._eth_tx_monitor):
        def eth_tx_monitor_cb(i, p):
            logger.debug(f"tx_eth{i} packet transmitted: len={len(p)}, data={bytes(p).hex()}")
        tx.add_callback(partial(eth_tx_monitor_cb, i))

    count = 1
    for i in range(count):
        pkt = bytes([(i % 256) for i in range(72 + i)])
        await e(nfb.ndp.tx[0].sendmsg)([(pkt, bytes(), 0)])

    await Timer(20, unit='us')
    stats = await e(nfb.eth[0].txmac.read_stats)()
    assert stats['passed'] == count, f"Packet count mismatch: {stats['passed']}, expected {count}"


async def _test_ndp_sendmsg_burst(dut, dev=None, nfb=None):
    if dev is None:
        dev, nfb = await get_dev(dut)

    for eth in nfb.eth:
        await e(eth.txmac.reset_stats)()
        await e(eth.txmac.enable)()

    for i, tx in enumerate(dev._eth_tx_monitor):
        def eth_tx_monitor_cb(i, p):
            logger.debug(f"tx_eth{i} packet transmitted: len={len(p)}, data={bytes(p).hex()}")
        tx.add_callback(partial(eth_tx_monitor_cb, i))

    pkts = range(20, 28)
    for i in pkts:
        pkt = bytes([(i % 256) for i in range(72 + i)])
        await e(nfb.ndp.tx[0].sendmsg)([(pkt, bytes(), 0)])

    await Timer(15, unit='us')
    stats = await e(nfb.eth[0].txmac.read_stats)()
    assert stats['passed'] == len(pkts), f"{stats['passed']}"


@cocotb.test(timeout_time=400, timeout_unit='us', skip=False)
async def test_ndp_send_msgs(dut):
    dev, nfb = await get_dev(dut)

    # FIXME: tests doesn't shuts DMA
    await _test_ndp_sendmsg(dut, dev, nfb)
    await _test_ndp_sendmsg(dut, dev, nfb)
    await _test_ndp_sendmsg_burst(dut, dev, nfb)


core = NFBDevice.core_instance_from_top(cocotb.top)

pcic = core.pcie_i.pcie_core_i
#ms.cmd(f"log -recursive {ms.cocotb2path(core)}/*")
#ms.cmd(f"log -recursive {ms.cocotb2path(core)}/pcie_i/*")
#ms.cmd(f"log -recursive {ms.cocotb2path(core)}/dma_i/dma_i/*")
#ms.cmd(f"log -recursive {ms.cocotb2path(core)}/app_i/*")
#ms.cmd(f"log -recursive {ms.cocotb2path(core)}/network_mod_i/*")

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
    #MfbBus(core.app_i, "DMA_RX_MFB", i, slices=DMA_STREAMS).add_wave(groups=["APP_DMA_RX_MFB", i], expand=[1])
    #MfbBus(core.app_i, "DMA_TX_MFB", i, slices=DMA_STREAMS).add_wave(groups=["APP_DMA_TX_MFB", i], expand=[1])

for i in range(DMA_ENDPOINTS):
    DmaUpMvbBus(core.dma_i, 'PCIE_RQ_MVB', i).add_wave(groups=["DMA2PCIe", "RQ MVB", i], expand=[2, 3])
    MfbBus(core.dma_i, 'PCIE_RQ_MFB', i).add_wave(groups=["DMA2PCIe", "RQ MFB", i], expand=[2])
    DmaDownMvbBus(core.dma_i, 'PCIE_RC_MVB', i).add_wave(groups=["DMA2PCIe", "RC MVB", i], expand=[2, 3])
    MfbBus(core.dma_i, 'PCIE_RC_MFB', i).add_wave(groups=["DMA2PCIe", "RC MFB", i], expand=[2])

clk_eth = SignalProxy(core.app_i.CLK_ETH, 0)

ms.add_wave(clk_eth)
for i in range(ETH_STREAMS):
    MfbBus(core.app_i, 'ETH_RX_MFB', i, label=f"ETH_RX_MFB{i}").add_wave()
    MfbBus(core.app_i, 'ETH_TX_MFB', i, label=f"ETH_TX_MFB{i}").add_wave()
