import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer, RisingEdge, FallingEdge, Combine
from cocotb.utils import get_sim_steps

from cocotb import simulator

from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster, Axi4StreamSlave
from cocotbext.ofm.axi4stream.monitors import Axi4Stream
from cocotbext.ofm.avst_pcie.drivers import AvstPcieDriverMaster, AvstPcieDriverSlave
from cocotbext.ofm.avst_pcie.monitors import AvstPcieMonitor

from cocotbext.ofm.pcie import Axi4SCompleter
from cocotbext.ofm.pcie import Axi4SRequester
from cocotbext.ofm.pcie import AvstCompleter
from cocotbext.ofm.pcie import AvstRequester

import cocotbext.nfb
from cocotbext.ofm.lbus.monitors import LBusMonitor
from cocotbext.ofm.lbus.drivers import LBusDriver
from cocotbext.ofm.avst_eth.monitors import AvstEthMonitor
from cocotbext.ofm.avst_eth.drivers import AvstEthDriver

class Axi4StreamMasterV(Axi4StreamMaster):
    _signals = {"TVALID": "VALID"}
    _optional_signals = {"TREADY": "READY", "TDATA": "DATA", "TLAST": "LAST", "TKEEP" :"KEEP", "TUSER": "USER"}
class Axi4StreamSlaveV(Axi4StreamSlave):
    _signals = {"TVALID": "VALID"}
    _optional_signals = {"TREADY": "READY", "TDATA": "DATA", "TLAST": "LAST", "TKEEP" :"KEEP", "TUSER": "USER"}
class Axi4StreamV(Axi4Stream):
    _signals = {"TVALID": "VALID"}
    _optional_signals = {"TREADY": "READY", "TDATA": "DATA", "TLAST": "LAST", "TKEEP" :"KEEP", "TUSER": "USER"}


class NFBDevice(cocotbext.nfb.NfbDevice):
    @staticmethod
    def core_instance_from_top(dut):
        try:
            core = [getattr(dut, core) for core in ["usp_i", "fpga_i", "ag_i", "cm_i"] if hasattr(dut, core)][0]
        except:
            # No fpga_common instance in card, try fpga_common directly
            core = dut

        return core

    async def _init_clks(self):
        self._core = NFBDevice.core_instance_from_top(self._dut)
        if self._card_name == "FB2CGHH":
            await cocotb.start(Clock(self._dut.REFCLK, 20, 'ns').start())
        elif self._card_name in ["FB2CGG3", "FB4CGG3"]:
            await cocotb.start(Clock(self._dut.REFCLK, 20, 'ns').start())
            await cocotb.start(Clock(self._dut.QSFP0_REFCLK_P, 6.206, 'ns').start())
            await cocotb.start(Clock(self._dut.QSFP0_REFCLK_N, 6.206, 'ns').start(start_high=False))
        elif self._card_name == "NFB-200G2QL":
            await cocotb.start(Clock(self._dut.SYSCLK_P, 8, 'ns').start())
            await cocotb.start(Clock(self._dut.SYSCLK_N, 8, 'ns').start(start_high=False))
        elif "AGI-FH400G" in self._card_name:
            # FIXME: Check freq
            await cocotb.start(Clock(self._dut.AG_SYSCLK0_P, 8, 'ns').start())
            await cocotb.start(Clock(self._dut.AG_SYSCLK1_P, 8, 'ns').start())
            raise NotImplementedError("This card doesn't run")
        elif self._card_name == "N6010":
            await cocotb.start(Clock(self._dut.SYS_CLK_100M, 10, 'ns').start())
            self._core.clk_gen_i.LOCKED.value = 1
            self._core.clk_gen_i.INIT_DONE_N.value = 0
        elif self._card_name == "VCU118":
            await cocotb.start(Clock(self._dut.REFCLK_P, get_sim_steps(10/3 / 2, 'ns', round_mode='round')*2).start())
            await cocotb.start(Clock(self._dut.REFCLK_N, get_sim_steps(10/3 / 2, 'ns', round_mode='round')*2).start(start_high=False))

            await cocotb.start(Clock(self._dut.QSFP0_REFCLK_P, 6.4, 'ns').start())
            await cocotb.start(Clock(self._dut.QSFP0_REFCLK_N, 6.4, 'ns').start(start_high=False))
            await cocotb.start(Clock(self._dut.QSFP1_REFCLK_P, 6.4, 'ns').start())
            await cocotb.start(Clock(self._dut.QSFP1_REFCLK_N, 6.4, 'ns').start(start_high=False))
        elif self._card_name == "IA-420F":
            await cocotb.start(Clock(self._dut.USR_CLK_33M, get_sim_steps(1000/33 / 2, 'ns', round_mode='round')*2).start())
            await cocotb.start(Clock(self._dut.QSFP_REFCLK_156M, 6.4, 'ns').start())
        elif self._card_name == "DK-DEV-1SDX-P":
            await cocotb.start(Clock(self._dut.FPGA_SYSCLK0_100M_P, 10, 'ns').start())
            await cocotb.start(Clock(self._dut.CLK_156P25M_QSFP1_P, 6.4, 'ns').start())
        elif self._card_name == "DK-DEV-AGI027RES":
            await cocotb.start(Clock(self._dut.REFCLK_PCIE_14C_CH0_P, 10, 'ns').start())
            await cocotb.start(Clock(self._dut.REFCLK_CXL_15C_CH0_P, 10, 'ns').start())
            await cocotb.start(Clock(self._dut.REFCLK_FGT12ACH4_P, 6.4, 'ns').start())
            raise NotImplementedError("This card doesn't run")
        elif self._card_name == "ALVEO_U200":
            await cocotb.start(Clock(self._dut.SYSCLK_P, 6.4, 'ns').start())
            await cocotb.start(Clock(self._dut.SYSCLK_N, 6.4, 'ns').start(start_high=False))

            await cocotb.start(Clock(self._dut.QSFP0_REFCLK_P, 6.206, 'ns').start())
            await cocotb.start(Clock(self._dut.QSFP0_REFCLK_N, 6.206, 'ns').start(start_high=False))
            await cocotb.start(Clock(self._dut.QSFP1_REFCLK_P, 6.206, 'ns').start())
            await cocotb.start(Clock(self._dut.QSFP1_REFCLK_N, 6.206, 'ns').start(start_high=False))
        elif self._card_name == "ALVEO_U55C":
            await cocotb.start(Clock(self._dut.SYSCLK2_P, 10, 'ns').start())
            await cocotb.start(Clock(self._dut.SYSCLK2_N, 10, 'ns').start(start_high=False))
            await cocotb.start(Clock(self._dut.SYSCLK3_P, 10, 'ns').start())
            await cocotb.start(Clock(self._dut.SYSCLK3_N, 10, 'ns').start(start_high=False))
            await cocotb.start(Clock(self._dut.QSFP0_REFCLK_P, 6.206, 'ns').start())
            await cocotb.start(Clock(self._dut.QSFP0_REFCLK_N, 6.206, 'ns').start(start_high=False))
        else:
            # No card: fpga_common
            await cocotb.start(Clock(self._dut.SYSCLK, 10, 'ns').start())

        if self._card_name in ["IA-420F", "N6010", "DK-DEV-1SDX-P"]:
            await cocotb.start(Clock(self._core.clk_gen_i.OUTCLK_0, 2.5, 'ns').start())
            await cocotb.start(Clock(self._core.clk_gen_i.OUTCLK_1, get_sim_steps(10/3 / 2, 'ns', round_mode='round')*2).start())
            await cocotb.start(Clock(self._core.clk_gen_i.OUTCLK_2, 5, 'ns').start())
            await cocotb.start(Clock(self._core.clk_gen_i.OUTCLK_3, 10, 'ns').start())

        for pcie_clk in self._core.pcie_i.pcie_core_i.pcie_hip_clk:
            await cocotb.start(Clock(pcie_clk, 4, 'ns').start())

        for eth_core in self._core.network_mod_i.eth_core_g:
            if hasattr(eth_core.network_mod_core_i, 'cmac_clk_322m'):
                await cocotb.start(Clock(eth_core.network_mod_core_i.cmac_clk_322m, 3106, 'ps').start())
            if hasattr(eth_core.network_mod_core_i, 'etile_clk_out'):
                await cocotb.start(Clock(eth_core.network_mod_core_i.etile_clk_out, 2482, 'ps').start())

    def _init_pcie(self):
        handle = simulator.get_root_handle("combo_user_const")
        combo_user_const = cocotb.handle.SimHandle(handle)
        self._card_name = combo_user_const.CARD_NAME.value.decode()

        try:
            self._core = NFBDevice.core_instance_from_top(self._dut)
        except:
            # No fpga_common instance in card, try fpga_common directly
            self._core = self._dut

        pcie_i = self._core.pcie_i.pcie_core_i
        self.mi = []
        self.pcie_req = []

        for i, clk in enumerate(pcie_i.pcie_hip_clk):
            clk = pcie_i.pcie_hip_clk[i]
            #rst = pcie_i.pcie_hip_rst[i]
            if hasattr(pcie_i, "pcie_cq_axi_data"):
                cq  = Axi4StreamMasterV(pcie_i, "pcie_cq_axi", clk, array_idx=i)
                cc  = Axi4StreamSlaveV(pcie_i, "pcie_cc_axi", clk, array_idx=i)
                ccm = Axi4StreamV(pcie_i, "pcie_cc_axi", clk, 0, aux_signals=True, array_idx=i)

                rq  = Axi4StreamSlaveV(pcie_i, "pcie_rq_axi", clk, array_idx=i)
                rc  = Axi4StreamMasterV(pcie_i, "pcie_rc_axi", clk, array_idx=i)
                rqm = Axi4StreamV(pcie_i, "pcie_rq_axi", clk, aux_signals=True, array_idx=i)

                req = Axi4SRequester(self.ram, rq, rc, rqm)
                mi  = Axi4SCompleter(cq, cc, ccm)
                self.mi.append(mi)
                self.pcie_req.append(req)

            if hasattr(pcie_i, "pcie_avst_down_data"):
                cc_rq_drv = AvstPcieDriverSlave(pcie_i, "pcie_avst_up", clk, array_idx=i)
                cq_rc_drv = AvstPcieDriverMaster(pcie_i, "pcie_avst_down", clk, array_idx=i)

                cc_mon = AvstPcieMonitor(pcie_i, "pcie_avst_up", clk, 0, aux_signals=True, array_idx=i)
                rq_mon = AvstPcieMonitor(pcie_i, "pcie_avst_up", clk, aux_signals=True, array_idx=i)

                req = AvstRequester(self.ram, cc_rq_drv, cq_rc_drv, rq_mon)
                mi = AvstCompleter(cq_rc_drv, cc_rq_drv, cc_mon)
                self.mi.append(mi)
                self.pcie_req.append(req)

        self._eth_rx_driver = []
        self._eth_tx_monitor = []
        for i, eth_core in enumerate(self._core.network_mod_i.eth_core_g):
            if hasattr(eth_core.network_mod_core_i, 'cmac_tx_lbus_rdy'):
                eth_core.network_mod_core_i.cmac_tx_lbus_rdy.value = 1
                eth_core.network_mod_core_i.cmac_rx_local_fault.value = 0

                tx_monitor = LBusMonitor(eth_core.network_mod_core_i, "cmac_tx_lbus", eth_core.network_mod_core_i.cmac_clk_322m)
                rx_driver = LBusDriver(eth_core.network_mod_core_i, "cmac_rx_lbus", eth_core.network_mod_core_i.cmac_clk_322m)
                self._eth_tx_monitor.append(tx_monitor)
                self._eth_rx_driver.append(rx_driver)

            if hasattr(eth_core.network_mod_core_i, 'tx_avst_ready'):
                eth_core.network_mod_core_i.tx_avst_ready.value = 1
                # eth_core.network_mod_core_i.tx_ad_avst_error.value = 0

                tx_monitor = AvstEthMonitor(eth_core.network_mod_core_i, "tx_avst", eth_core.network_mod_core_i.etile_clk_out)
                rx_driver = AvstEthDriver(eth_core.network_mod_core_i, "rx_avst", eth_core.network_mod_core_i.etile_clk_out)
                self._eth_tx_monitor.append(tx_monitor)
                self._eth_rx_driver.append(rx_driver)

        self.dtb = None

    async def _reset(self, time=40, units="ns"):
        t = Timer(time, units)
        pcie_i = self._core.pcie_i.pcie_core_i
        if hasattr(pcie_i, 'pcie_hip_rst'):
            for rst in pcie_i.pcie_hip_rst:
                rst.value = 1
            await t
            for rst in pcie_i.pcie_hip_rst:
                rst.value = 0

            # FIXME: some strange loopback on ALVEO_U200
            if self._core.USE_PCIE_CLK.value == 1:
                await cocotb.triggers.FallingEdge(self._core.global_reset)
        elif hasattr(pcie_i, 'pcie_reset_status_n'):
            for rst in pcie_i.pcie_reset_status_n:
                rst.value = 0
            await t
            for rst in pcie_i.pcie_reset_status_n:
                rst.value = 1
        else:
            raise NotImplementedError("Unknown signals for PCI/device reset")

        if self._core.rst_pci[0].value == 1:
            await cocotb.triggers.FallingEdge(self._core.rst_pci[0])

    async def _pcie_cfg_ext_reg_access(self, addr, index = 0, fn = 0, sync=True, data=None):
        pcie_i = self._core.pcie_i.pcie_core_i
        clk = pcie_i.pcie_hip_clk[index]

        if sync:
            await RisingEdge(clk)

        pcie_i.cfg_ext_function[index].value = fn
        pcie_i.cfg_ext_register[index].value = addr >> 2
        pcie_i.cfg_ext_read[index].value = 1 if data == None else 0
        pcie_i.cfg_ext_write[index].value = 0 if data == None else 1
        if data:
            pcie_i.cfg_ext_write_data[index].value = data
        await RisingEdge(clk)
        pcie_i.cfg_ext_read[index].value = 0
        pcie_i.cfg_ext_write[index].value = 0
        if data == None:
            return pcie_i.cfg_ext_read_data[index].value.integer

    async def _pcie_cfg_ext_reg_read(self, addr, index = 0, fn = 0, sync=True):
        return await self._pcie_cfg_ext_reg_access(addr, index, fn, sync)

    async def _pcie_cfg_ext_reg_write(self, addr, data, index = 0, fn = 0, sync=True):
        await self._pcie_cfg_ext_reg_access(addr, index, fn, sync, data)

    async def _read_dtb_raw(self, cap_dtb = 0x480):
        dtb_length = await self._pcie_cfg_ext_reg_read(cap_dtb + 0x0c)
        data = []
        for i in range(dtb_length // 4):
            await self._pcie_cfg_ext_reg_write(cap_dtb + 0x10, i, sync=False)
            data.append(await self._pcie_cfg_ext_reg_read(cap_dtb + 0x14, sync=True))

        return bytes(sum([[(x >> 0) & 0xFF, (x >> 8) & 0xFF, (x >> 16) & 0xFF, (x >> 24) & 0xFF] for x in data], []))
