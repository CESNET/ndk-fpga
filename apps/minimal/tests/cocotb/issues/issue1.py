import cocotb
import cocotb.utils
from cocotb.triggers import Timer, RisingEdge, First

import cocotbext.ofm.utils.sim.modelsim as ms

from cocotbext.ofm.utils.sim.bus import MfbBus, DmaDownMvbBus
from cocotbext.ofm.utils.scapy import simple_tcp_bytes

from ndk_core import NFBDevice

print = ms.print

e = cocotb.external
st = cocotb.utils.get_sim_time

core = NFBDevice.core_instance_from_top(cocotb.top)


async def get_dev_init(dut):
    dev = NFBDevice(dut)
    await dev.init()
    return dev, dev.nfb


async def _rx_pkts(dev, nfb):
    for eth in nfb.eth:
        await e(eth.rxmac.enable)()

    await e(nfb.ndp.rx[0].start)()
    await dev.dma.rx[0]._push_desc()

    await Timer(2, units='us')

    pkt = simple_tcp_bytes()

    for i in range(10):
        await dev._eth_rx_driver[0].write_packet(list(pkt))


@cocotb.test()
async def reset_pci_inside_pkt_rx(dut):
    dev, nfb = await get_dev_init(dut)

    for eth in nfb.eth:
        await e(eth.rxmac.enable)()

    await _rx_pkts(dev, nfb)
    await dev._reset()
    await _rx_pkts(dev, nfb)


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


pci_core = core.pcie_i.pcie_core_i
ms.cmd(f"log -recursive {ms.cocotb2path(core)}/*")

ms.add_wave(core.global_reset)
ms.add_wave(pci_core.PCIE_USER_RESET)
ms.add_wave(pci_core.PCIE_USER_CLK)

ms.add_wave(core.pcie_i.MI_CLK)
ms.add_wave(core.pcie_i.MI_RESET)

#ms.add_wave(core.dma_i.MI_CLK)
#ms.add_wave(core.dma_i.MI_RESET)

ms.add_wave(core.dma_i.DMA_CLK)
ms.add_wave(core.dma_i.DMA_RESET)

ms.add_wave(core.dma_i.USR_CLK)
ms.add_wave(core.dma_i.USR_RESET)

#ms.add_wave(core.dma_i.CROX_CLK)
#ms.add_wave(core.dma_i.CROX_RESET)


MfbBus(core.dma_i, 'RX_USR_MFB', 0, label='DMA RX_MFB').add_wave()
#MfbBus(core.dma_i, 'TX_USR_MFB', 0).add_wave()

#DmaUpMvbBus(core.dma_i, 'PCIE_RQ_MVB', 0).add_wave()
#MfbBus(core.dma_i, 'PCIE_RQ_MFB', 0).add_wave()

DmaDownMvbBus(core.dma_i, 'PCIE_RC_MVB', 0).add_wave()
MfbBus(core.dma_i, 'PCIE_RC_MFB', 0).add_wave()

#MfbBus(pci_core, 'RC_MFB', 0).add_wave()
#MfbBus(pci_core, 'RQ_MFB', 0).add_wave()
#MfbBus(pci_core, 'CC_MFB', 0).add_wave()
#MfbBus(pci_core, 'CQ_MFB', 0).add_wave()
