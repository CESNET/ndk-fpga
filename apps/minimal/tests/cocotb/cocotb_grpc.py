# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

import logging
from cocotbext.ofm.utils import partial
import cocotb
from cocotb.triggers import Timer

import scapy.all
import scapy.utils
import scapy.volatile
import scapy.contrib.mpls

from cocotbext.ndk_core import NFBDevice

import cocotbext.ofm.utils.sim.modelsim as ms
import cocotb.utils

from cocotbext.ofm.utils.sim.bus import MfbBus, MiBus, DmaDownMvbBus, DmaUpMvbBus
from cocotbext.nfb.ext.grpc import RAM, NfbDmaThreadedGrpcServer


logger = logging.getLogger(__name__)
#logger.setLevel(logging.DEBUG)
logging.getLogger("cocotbext.nfb.ext.grpc.server").setLevel(logging.INFO)
#logging.getLogger("cocotbext.nfb.ext.grpc.nfb").setLevel(logging.DEBUG)
#logging.getLogger("cocotbext.ofm.pcie").setLevel(logging.DEBUG)


e = cocotb.external
st = cocotb.utils.get_sim_time


async def get_dev(dut, init=True, **kwargs):
    dev = NFBDevice(dut, **kwargs)
    if init:
        await dev.init()
    return dev, dev.nfb


@cocotb.test()
async def test_grpc(dut):
    ram = RAM()
    dev, nfb = await get_dev(dut, ram=ram)

    #for eth in nfb.eth:
    #    await e(eth.rxmac.enable)()

    # Generate packets on RX eth
    async def rx_packet(eth, count):
        for _ in range(count):
            pkt = scapy.all.Ether()/scapy.all.IP(dst="127.0.0.1")/scapy.all.TCP()/"GET /index.html HTTP/1.0 \n\n"
            await eth.write_packet(list(bytes(pkt)))

    for rx in dev._eth_rx_driver:
        cocotb.start_soon(rx_packet(rx, 50000))

    # Log packets on TX eth
    for i, tx in enumerate(dev._eth_tx_monitor):
        def eth_tx_monitor_cb(i, p):
            logger.debug(f"tx_eth{i} packet transmitted: len={len(p)}, data={bytes(p).hex()}")
        tx.add_callback(partial(eth_tx_monitor_cb, i))

    # Run gRPC server with Nfb and Dma services usable for libnfb-ext-grpc
    with NfbDmaThreadedGrpcServer(ram, dev):
        await Timer(10, units='ms')


core = NFBDevice.core_instance_from_top(cocotb.top)

pcic = core.pcie_i.pcie_core_i
#ms.cmd(f"log -recursive {ms.cocotb2path(core)}/*")
#ms.cmd(f"log -recursive {ms.cocotb2path(core)}/pcie_i/*")
#ms.cmd(f"log -recursive {ms.cocotb2path(core)}/dma_i/dma_i/*")
#ms.cmd(f"log -recursive {ms.cocotb2path(core)}/app_i/*")
#ms.cmd(f"log -recursive {ms.cocotb2path(core)}/network_mod_i/*")

DMA_STREAMS = core.dma_i.DMA_STREAMS.value
DMA_ENDPOINTS = core.dma_i.DMA_ENDPOINTS.value

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
    MfbBus(core.dma_i, 'PCIE_RQ_MFB', i).add_wave(groups=["DMA2PCIe", "RC MFB", i], expand=[2])

ms.add_wave(core.app_i.CLK_ETH[0])
for i in range(2):
    MfbBus(core.app_i, 'ETH_RX_MFB', i, label=f"ETH_RX_MFB{i}").add_wave()
    MfbBus(core.app_i, 'ETH_TX_MFB', i, label=f"ETH_TX_MFB{i}").add_wave()
