import sys
import cocotb
import logging
from cocotb.triggers import Timer, RisingEdge, Combine, Join, First, with_timeout

from ndk_core import NFBDevice

import cocotbext.ofm.utils.sim.modelsim as ms
import cocotb.utils

e = cocotb.external
st = cocotb.utils.get_sim_time


async def get_dev(dut, init=True):
    dev = NFBDevice(dut)
    if init:
        await dev.init()
    # dev._servicer._log.setLevel(logging.DEBUG)
    return dev, dev.nfb


@cocotb.test(timeout_time=200, timeout_unit='us')
async def test_mi_access_unaligned(dut):
    dev, nfb = await get_dev(dut)
    c = nfb.comp_open("cesnet,ofm,mi_test_space")

    await e(c.read)(0, 1)

    #for i in range(46, 64): # FIXME: Test fails (for US+)
    for i in range(24, 42):
        for x in range(0, 5):
            data = bytes([(j%256) for j in range(i)])
            await e(c.write)(x, data)
            rdata = await e(c.read)(x, len(data))
            assert data == rdata, f"{list(data)}, {list(rdata)}"


@cocotb.test(timeout_time=50, timeout_unit='us')
async def test_enable_rxmac_and_check_status(dut):
    dev, nfb = await get_dev(dut)

    mac = nfb.eth[0].rxmac
    await e(mac.enable)()
    await e(mac.is_enabled)()
    await e(nfb.ndp.rx[0].read_stats)()


@cocotb.test(timeout_time=200, timeout_unit='us')
async def test_ndp_recvmsg(dut):
    dev, nfb = await get_dev(dut)
    for eth in nfb.eth:
        await e(eth.rxmac.enable)()

    await e(nfb.ndp.rx[0].start)()
    await dev.dma.rx[0]._push_desc()
    await Timer(2, units='us')

    #pkt = bytes(raw(Ether()/IP(dst="127.0.0.1")/TCP()/"GET /index.html HTTP/1.0 \n\n"))
    pkt = bytes([i for i in range(72)])

    await dev._eth_rx_driver[0].write_packet(list(pkt))
    await Timer(105, units='us')

    recv = await e(nfb.ndp.rx[0].recv)()
    # FIXME: try again for slower cards
    #if [pkt] != recv:
    #    await Timer(85, units='us')
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

    pkt = bytes([i for i in range(72)])
    def eth_tx_monitor_cb(p):
        print(len(p), bytes(p).hex())
        #assert bytes(p) == pkt

    dev._eth_tx_monitor[0].add_callback(eth_tx_monitor_cb)

    count = 1
    for i in range(count):
        pkt = bytes([(i%256) for i in range(72 + i)])
        await e(nfb.ndp.tx[0].sendmsg)([(pkt, bytes(), 0)])

    await Timer(20, units='us')
    stats = await e(nfb.eth[0].txmac.read_stats)()
    assert stats['passed'] == count, f"Packet count mismatch: {stats['passed']}, expected {count}"


async def _test_ndp_sendmsg_burst(dut, dev=None, nfb=None):
    if dev is None:
        dev, nfb = await get_dev(dut)

    for eth in nfb.eth:
        await e(eth.txmac.reset_stats)()
        await e(eth.txmac.enable)()

    def eth_tx_monitor_cb(p):
        print(len(p), bytes(p).hex())
        sys.stdout.flush()

    dev._eth_tx_monitor[0].add_callback(eth_tx_monitor_cb)

    pkts = range(20, 28)
    for i in pkts:
        pkt = bytes([(i%256) for i in range(72 + i)])
        await e(nfb.ndp.tx[0].sendmsg)([(pkt, bytes(), 0)])

    await Timer(15, units='us')
    stats = await e(nfb.eth[0].txmac.read_stats)()
    assert stats['passed'] == len(pkts), f"{stats['passed']}"


@cocotb.test(timeout_time=400, timeout_unit='us')
async def test_ndp_send_msgs(dut):
    dev, nfb = await get_dev(dut)
    # FIXME: tests doesn't shuts DMA
    await _test_ndp_sendmsg(dut, dev, nfb)
    await _test_ndp_sendmsg(dut, dev, nfb)
    await _test_ndp_sendmsg_burst(dut, dev, nfb)


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
MiBus(core.pcie_i, 'MI', 0, label='MI_PCIe').add_wave()
#MiBus(core.dma_i, 'MI', 0, label='MI_DMA').add_wave()


ms.add_wave(core.pcie_i.MI_CLK)
ms.add_wave(core.pcie_i.MI_RESET)
ms.add_wave(core.dma_i.MI_CLK)
ms.add_wave(core.dma_i.MI_RESET)
ms.add_wave(core.global_reset)
