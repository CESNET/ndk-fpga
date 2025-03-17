# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

#import sys
import logging

import cocotb
from cocotb.triggers import Timer

import scapy.all
import scapy.utils
import scapy.volatile
import scapy.contrib.mpls

from ndk_core import NFBDevice

import cocotbext.ofm.utils.sim.modelsim as ms
import cocotb.utils

from cocotbext.ofm.utils.sim.bus import MfbBus, MiBus
from cocotbext.nfb.ext.grpc import RAM, NfbDmaThreadedGrpcServer


#logging.basicConfig(stream=sys.stderr, force=True)
#logging.getLogger().setLevel(logging.DEBUG)

logger = logging.getLogger(__name__)

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

    # Generate packets on RX eth
    async def rx_packet(eth, count):
        for _ in range(count):
            pkt = scapy.all.Ether()/scapy.all.IP(dst="127.0.0.1")/scapy.all.TCP()/"GET /index.html HTTP/1.0 \n\n"
            await eth.write_packet(list(bytes(pkt)))

    for rx in dev._eth_rx_driver:
        cocotb.start_soon(rx_packet(rx, 50000))

    # Log packets on TX eth
    for i, tx in enumerate(dev._eth_tx_monitor):
        def eth_tx_monitor_cb(p):
            logger.debug(f"tx_eth{i} packet transmitted: len={len(p)}, data={bytes(p).hex()}")
        tx.add_callback(eth_tx_monitor_cb)

    # Run gRPC server with Nfb and Dma services usable for libnfb-ext-grpc
    with NfbDmaThreadedGrpcServer(ram, dev):
        await Timer(10, units='ms')


core = NFBDevice.core_instance_from_top(cocotb.top)

pcic = core.pcie_i.pcie_core_i
#ms.cmd(f"log -recursive {ms.cocotb2path(core)}/*")

ms.add_wave(core.pcie_i.MI_RESET)
ms.add_wave(core.pcie_i.MI_CLK)
MiBus(core.pcie_i, 'MI', 0, label='MI_PCIe').add_wave()

ms.add_wave(core.app_i.MI_CLK)
MiBus(core.app_i, 'MI', label='MI_APP').add_wave()

ms.add_wave(core.app_i.CLK_ETH[0])
MfbBus(core.app_i, 'ETH_RX_MFB', 0).add_wave()
MfbBus(core.app_i, 'ETH_TX_MFB', 0).add_wave()

ms.add_wave(core.app_i.DMA_CLK)
MfbBus(core.app_i, 'DMA_RX_MFB', 0).add_wave()
MfbBus(core.app_i, 'DMA_TX_MFB', 0).add_wave()
