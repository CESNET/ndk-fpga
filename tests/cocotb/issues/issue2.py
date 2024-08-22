import sys
import logging

import cocotb
import cocotb.utils
from cocotb.triggers import Timer, RisingEdge, Combine, Join, First, with_timeout

import cocotbext.ofm.utils.sim.modelsim as ms

from cocotbext.ofm.utils.sim.bus import *
from cocotbext.ofm.utils.scapy import simple_tcp_bytes

from ndk_core import NFBDevice

print = ms.print

e = cocotb.external
st = cocotb.utils.get_sim_time

def ms_add_cursor(name, time=None):
    if time is None:
        time = st()

    ms.cmd(f"wave cursor add")
    ms.cmd(f'wave cursor configure -name {{{name}}} -time {{{time}}} -lock 1')


async def wr_rd(c, length):
    data = bytes([(j%256) for j in range(length)])
    await e(c.write)(0, data)
    rdata = await e(c.read)(0, length)
    assert rdata == data, f'writen: {list(data)}, readen: {list(rdata)}'

@cocotb.test()
async def mtc_big_write_tr(dut):
    ms_add_cursor("CQ WR REQ", "0.1us")
    ms_add_cursor("CQ RD REQ", "0.104us")
    ms_add_cursor("bad cq_data ", "1.42us")

    dev = NFBDevice(dut)
    await dev.init()
    c = dev.nfb.comp_open("cesnet,ofm,mi_test_space")

    # This one will pass through
    #await wr_rd(c, 32)

    # This one transfers correctly 32B, 4B incorrectly and then stucks!
    await with_timeout(
        wr_rd(c, 36),
        10, 'us',
    )
    )



core = NFBDevice.core_instance_from_top(cocotb.top)

pci_core = core.pcie_i.pcie_core_i

MiBus(core.pcie_i, 'MI', 0, label='MI_PCIe').add_wave()
ms.cmd(f"log -recursive {ms.cocotb2path(core)}/*")
ms.cmd('add wave sim:/fpga/cm_i/pcie_i/pcie_ctrl_g(0)/pcie_ctrl_i/mtc_i/*')
