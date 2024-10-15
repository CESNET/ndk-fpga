import cocotb
import cocotb.utils

import cocotbext.ofm.utils.sim.modelsim as ms

from cocotbext.ofm.utils.sim.bus import MiBus

from ndk_core import NFBDevice

print = ms.print

e = cocotb.external
st = cocotb.utils.get_sim_time


def ms_add_cursor(name, time=None):
    if time is None:
        time = st()

    ms.cmd("wave cursor add")
    ms.cmd(f'wave cursor configure -name {{{name}}} -time {{{time}}} -lock 1')


async def get_dev_init(dut):
    dev = NFBDevice(dut)
    await dev.init()
    return dev, dev.nfb


async def wr_rd(c, length, offset=0):
    data = bytes([(j % 256) for j in range(length)])
    await e(c.write)(offset, data)
    rdata = await e(c.read)(offset, length)
    assert rdata == data, f'writen: {list(data)}, readen: {list(rdata)}'


@cocotb.test(timeout_time=400, timeout_unit='us')
async def mtc_big_write_tr(dut):
    dev, nfb = await get_dev_init(dut)
    c = nfb.comp_open("cesnet,ofm,mi_test_space")

    await wr_rd(c, 126, 3)


core = NFBDevice.core_instance_from_top(cocotb.top)
core_path = ms.cocotb2path(core)

pci_core = core.pcie_i.pcie_core_i
MiBus(core.pcie_i, 'MI', 0, label='MI_PCIe').add_wave()
ms.cmd(f"log -recursive {core_path}/*")
ms.cmd(f'add wave {core_path}/pcie_i/pcie_ctrl_g(0)/pcie_ctrl_i/mtc_i/*')
