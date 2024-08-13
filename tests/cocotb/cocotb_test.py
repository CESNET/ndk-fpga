import sys
import cocotb
import logging
from cocotb.triggers import Timer, RisingEdge, Combine, Join, First, with_timeout

from ndk_core import NFBDevice

import cocotbext.ofm.utils.sim.modelsim as ms
import cocotb.utils

e = cocotb.external
st = cocotb.utils.get_sim_time

async def get_dev_init(dut):
    dev = NFBDevice(dut)
    await dev.init()
    return dev, dev.nfb

async def reset_after(nfb, time, units='ns'):
    await Timer(time, units)
    await nfb._reset()

@cocotb.test(skip=False)
async def cocotb_test_enable_rxmac_and_check_status(dut):
    sys.stdout.flush()
    await Timer(1, units='us')

    sys.stdout.flush()

    dev, nfb = await get_dev_init(dut)

    mac = nfb.eth[0].rxmac
    await e(mac.enable)()
    await e(mac.is_enabled)()
    await e(nfb.ndp.rx[0].read_stats)()


@cocotb.test(skip=True)
async def cocotb_test_reset_pcie_and_check_cc_idle(dut):
    dev, nfb = await get_dev_init(dut)

    # Do a transaction first
    mac = nfb.eth[0].rxmac
    await e(mac.enable)()
    await e(mac.is_enabled)()

    await Timer(1, units='us')

    tvalid = dev.mi[0]._cc.bus.TVALID

    # Check for value before reset
    assert tvalid.value == 0

    reset = cocotb.start_soon(dev._reset())
    cc_tvalid_rise = RisingEdge(tvalid)
    timer = Timer(5, units='us')

    # Check that reset completes without signal rising
    assert await First(cc_tvalid_rise, reset) != cc_tvalid_rise
    # Check that after reset the signal doesn't rise for some time
    assert await First(cc_tvalid_rise, timer) != cc_tvalid_rise

@cocotb.test(skip=True)
async def cocotb_test_reset_pcie_and_check_rq_idle(dut):
    dev, nfb = await get_dev_init(dut)

    # Generate some transactions
    await dev.dma.rx[0]._push_desc()
    await Timer(1, units='us')

    # Signal to check
    tvalid = dev.pcie_req[0]._rq.bus.TVALID

    assert tvalid.value == 0, "tvalid was active before reset"

    reset = cocotb.start_soon(dev._reset())
    cc_tvalid_rise = RisingEdge(tvalid)
    timer = Timer(5, units='us')

    assert await First(cc_tvalid_rise, reset) != cc_tvalid_rise, "tvalid rises before reset done"
    assert await First(cc_tvalid_rise, timer) != cc_tvalid_rise, "tvalid rises too eraly after reset"

async def _cocotb_test_ndp_sendmsg(dev, nfb):
    for eth in nfb.eth:
        await e(eth.txmac.enable)()

    pkt = bytes([i for i in range(72)])
    def eth_tx_monitor_cb(p):
        assert bytes(p) == pkt

    dev._eth_tx_monitor[0].add_callback(eth_tx_monitor_cb)

    await e(nfb.ndp.tx[0].sendmsg)([(pkt, bytes(), 0)])

    await Timer(5, units='us')
    stats = await e(nfb.eth[0].txmac.read_stats)()
    assert stats['passed'] == 1

async def _cocotb_test_ndp_recvmsg(dev, nfb):
    for eth in nfb.eth:
        await e(eth.rxmac.enable)()

    await e(nfb.ndp.rx[0].start)()
    await dev.dma.rx[0]._push_desc()
    await Timer(2, units='us')

    #pkt = bytes(raw(Ether()/IP(dst="127.0.0.1")/TCP()/"GET /index.html HTTP/1.0 \n\n"))
    pkt = bytes([i for i in range(72)])

    await dev._eth_rx_driver[0].write_packet(list(pkt))
    await Timer(85, units='us')

    recv = await e(nfb.ndp.rx[0].recv)()
    assert [pkt] == recv

#@cocotb.test()
async def cocotb_test_ndp_sendmsg(dut):
    dev, nfb = await get_dev_init(dut)
    _cocotb_test_ndp_sendmsg(dev, nfb)

#@cocotb.test()
async def cocotb_test_ndp_recvmsg(dut):
    dev, nfb = await get_dev_init(dut)
    await _cocotb_test_ndp_recvmsg(dev, nfb)


#@cocotb.test()
async def _cocotb_test_ndp_rxmac_10pct(dev, nfb):
    from cocotbext.ofm.utils.scapy import s2b
    from scapy.all import TCP, Ether, IP, Raw

    for eth in nfb.eth:
        await e(eth.rxmac.enable)()

    await e(nfb.ndp.rx[0].start)()
    await dev.dma.rx[0]._push_desc()
    await Timer(2, units='us')

    pkt = Ether()/IP(dst="127.0.0.1")/TCP()/"GET /index.html HTTP/1.0 \n\n"
    pkt = pkt / Raw(" " * (128 - len(pkt)))
    pkt = s2b(pkt)

    for i in range(10):
        t_start = st()
        await dev._eth_rx_driver[0].write_packet(list(pkt))
        t_end = st()
        await Timer((t_end - t_start) * 9, units='ps')

    await Timer(85, units='us')

    recv = await e(nfb.ndp.rx[0].recv)()
    assert [pkt] == recv

# FIXME: workaround: currently the device can be reseted only once in simulation run when using DMA
@cocotb.test()
async def cocotb_test_ndp_sendmsg_and_recvmsg(dut):
    dev, nfb = await get_dev_init(dut)
    await _cocotb_test_ndp_sendmsg(dev, nfb)
    await _cocotb_test_ndp_recvmsg(dev, nfb)
    #await _cocotb_test_ndp_rxmac_10pct(dev, nfb)


from cocotbext.ofm.utils.sim.bus import *

core = NFBDevice.core_instance_from_top(cocotb.top)

pcic = core.pcie_i.pcie_core_i
#ms.cmd(f"log -recursive {ms.cocotb2path(core)}/*")

MfbBus(core.dma_i, 'RX_USR_MFB', 0).add_wave()
MfbBus(core.dma_i, 'TX_USR_MFB', 0).add_wave()

DmaUpMvbBus(core.dma_i, 'PCIE_RQ_MVB', 0).add_wave()
MfbBus(core.dma_i, 'PCIE_RQ_MFB', 0).add_wave()

DmaDownMvbBus(core.dma_i, 'PCIE_RC_MVB', 0).add_wave()
MfbBus(core.dma_i, 'PCIE_RC_MFB', 0).add_wave()

#MfbBus(pcic, 'RC_MFB', 0).add_wave()
#MfbBus(pcic, 'RQ_MFB', 0).add_wave()
#MfbBus(pcic, 'CC_MFB', 0).add_wave()
#MfbBus(pcic, 'CQ_MFB', 0).add_wave()
#MiBus(core.pcie_i, 'MI', 0, label='MI_PCIe').add_wave()
MiBus(core.dma_i, 'MI', 0, label='MI_DMA').add_wave()

MfbBus(core.dma_i, 'RX_USR_MFB').add_wave()
MfbBus(core.dma_i, 'RX_USR_MFB').add_wave()


ms.add_wave(core.pcie_i.MI_CLK)
ms.add_wave(core.pcie_i.MI_RESET)
ms.add_wave(core.dma_i.MI_CLK)
ms.add_wave(core.dma_i.MI_RESET)
ms.add_wave(core.global_reset)
