# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2024-2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Martin Spinler <spinler@cesnet.cz>

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer, RisingEdge, FallingEdge
from cocotb.utils import get_sim_steps
from cocotb.handle import Force

from cocotb import simulator

from cocotbext.ofm.base.bus_fixup import SignalProxy

from cocotbext.ofm.axi4s_pcie.drivers import Axi4sPcieDriverMaster, Axi4sPcieDriverSlave
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

from cocotbext.ofm.mac_segmented.drivers import MAC_Segmented_RX_Driver
from cocotbext.ofm.mac_segmented.monitors import MAC_Segmented_TX_Monitor

from cocotbext.ofm.avst_pcie.creditor import AvstCreditorRX, AvstCreditorTX, AvstCreditRequester, AvstCreditReceiver


class Axi4StreamV(Axi4Stream):
    _signals = {"TVALID": "VALID"}
    _optional_signals = {"TREADY": "READY", "TDATA": "DATA", "TLAST": "LAST", "TKEEP": "KEEP", "TUSER": "USER"}


class NFBDevice(cocotbext.nfb.NfbDevice):
    @staticmethod
    def core_instance_from_top(dut):
        try:
            core = [getattr(dut, core) for core in ["usp_i", "fpga_i", "ag_i", "cm_i"] if hasattr(dut, core)][0]
        except Exception:
            # No fpga_common instance in card, try fpga_common directly
            core = dut

        return core

    async def _init_clks(self):
        self._core = NFBDevice.core_instance_from_top(self._dut)
        if self._card_name == "FB2CGHH":
            cocotb.start_soon(Clock(self._dut.REFCLK, 20, 'ns').start())
        elif self._card_name in ["FB2CDG1", "FB2CDG1-VAR0", "FB2CDG1-VAR1"]:
            cocotb.start_soon(Clock(self._dut.SYSCLK_100_P, 10, 'ns').start())
        elif self._card_name in ["FB2CGG3", "FB4CGG3"]:
            cocotb.start_soon(Clock(self._dut.REFCLK, 20, 'ns').start())
            cocotb.start_soon(Clock(self._dut.QSFP0_REFCLK_P, 6.206, 'ns').start())
            cocotb.start_soon(Clock(self._dut.QSFP0_REFCLK_N, 6.206, 'ns').start(start_high=False))
        elif self._card_name == "NFB-200G2QL":
            cocotb.start_soon(Clock(self._dut.SYSCLK_P, 8, 'ns').start())
            cocotb.start_soon(Clock(self._dut.SYSCLK_N, 8, 'ns').start(start_high=False))
        elif self._card_name in ["AGI-FH400G", "AGI-FH400G-REV0", "AGI-FH400G-REV1", "AGI-FH400G-REV2"]:
            cocotb.start_soon(Clock(self._dut.AG_SYSCLK0_P, 8, 'ns').start())
            cocotb.start_soon(Clock(self._dut.AG_SYSCLK1_P, 10, 'ns').start())
        elif self._card_name in ["IA-440I", "IA-440I-VAR0", "IA-440I-VAR1"]:
            cocotb.start_soon(Clock(self._dut.SYS_CLK_100M, 10, 'ns').start())
        elif "IA-860M" in self._card_name:
            cocotb.start_soon(Clock(self._dut.SYSCLK_100_P, 10, 'ns').start())
        elif "A2700" in self._card_name:
            cocotb.start_soon(Clock(self._dut.AG_SYSCLK1_P, 20, 'ns').start())
        elif self._card_name in ["N6010", "N5014"]:
            cocotb.start_soon(Clock(self._dut.SYS_CLK_100M, 10, 'ns').start())
            self._core.clk_gen_i.LOCKED.value = 1
            self._core.clk_gen_i.INIT_DONE_N.value = 0
        elif self._card_name == "VCU118":
            cocotb.start_soon(Clock(self._dut.REFCLK_P, get_sim_steps(10/3 / 2, 'ns', round_mode='round')*2).start())
            cocotb.start_soon(Clock(self._dut.REFCLK_N, get_sim_steps(10/3 / 2, 'ns', round_mode='round')*2).start(start_high=False))

            cocotb.start_soon(Clock(self._dut.QSFP0_REFCLK_P, 6.4, 'ns').start())
            cocotb.start_soon(Clock(self._dut.QSFP0_REFCLK_N, 6.4, 'ns').start(start_high=False))
            cocotb.start_soon(Clock(self._dut.QSFP1_REFCLK_P, 6.4, 'ns').start())
            cocotb.start_soon(Clock(self._dut.QSFP1_REFCLK_N, 6.4, 'ns').start(start_high=False))
        elif self._card_name == "IA-420F":
            cocotb.start_soon(Clock(self._dut.USR_CLK_33M, get_sim_steps(1000/33 / 2, 'ns', round_mode='round')*2).start())
            cocotb.start_soon(Clock(self._dut.QSFP_REFCLK_156M, 6.4, 'ns').start())
        elif self._card_name == "DK-DEV-1SDX-P":
            cocotb.start_soon(Clock(self._dut.FPGA_SYSCLK0_100M_P, 10, 'ns').start())
            cocotb.start_soon(Clock(self._dut.CLK_156P25M_QSFP1_P, 6.4, 'ns').start())
        elif self._card_name == "DK-DEV-AGI027RES":
            cocotb.start_soon(Clock(self._dut.REFCLK_PCIE_14C_CH0_P, 10, 'ns').start())
            cocotb.start_soon(Clock(self._dut.REFCLK_CXL_15C_CH0_P, 10, 'ns').start())
            cocotb.start_soon(Clock(self._dut.REFCLK_FGT12ACH4_P, 6.4, 'ns').start())
            raise NotImplementedError("This card doesn't run")
        elif self._card_name == "ALVEO_U200":
            cocotb.start_soon(Clock(self._dut.SYSCLK_P, 6.4, 'ns').start())
            cocotb.start_soon(Clock(self._dut.SYSCLK_N, 6.4, 'ns').start(start_high=False))

            cocotb.start_soon(Clock(self._dut.QSFP0_REFCLK_P, 6.206, 'ns').start())
            cocotb.start_soon(Clock(self._dut.QSFP0_REFCLK_N, 6.206, 'ns').start(start_high=False))
            cocotb.start_soon(Clock(self._dut.QSFP1_REFCLK_P, 6.206, 'ns').start())
            cocotb.start_soon(Clock(self._dut.QSFP1_REFCLK_N, 6.206, 'ns').start(start_high=False))
        elif self._card_name == "ALVEO_U55C":
            cocotb.start_soon(Clock(self._dut.SYSCLK2_P, 10, 'ns').start())
            cocotb.start_soon(Clock(self._dut.SYSCLK2_N, 10, 'ns').start(start_high=False))
            cocotb.start_soon(Clock(self._dut.SYSCLK3_P, 10, 'ns').start())
            cocotb.start_soon(Clock(self._dut.SYSCLK3_N, 10, 'ns').start(start_high=False))
            cocotb.start_soon(Clock(self._dut.QSFP0_REFCLK_P, 6.206, 'ns').start())
            cocotb.start_soon(Clock(self._dut.QSFP0_REFCLK_N, 6.206, 'ns').start(start_high=False))
        else:
            # No card: fpga_common
            cocotb.start_soon(Clock(self._dut.SYSCLK, 10, 'ns').start())

        # Workaround for all Intel PLL/CLOCKGEN
        if any([(name in self._card_name) for name in ["IA-420F", "N6010", "N5014", "DK-DEV-1SDX-P", "AGI-FH400G", "IA-440I", "IA-860M", "A2700", "FB2CDG1"]]):
            cocotb.start_soon(Clock(self._core.clk_gen_i.OUTCLK_0, 2.5, 'ns').start())
            cocotb.start_soon(Clock(self._core.clk_gen_i.OUTCLK_1, get_sim_steps(10/3 / 2, 'ns', round_mode='round')*2).start())
            cocotb.start_soon(Clock(self._core.clk_gen_i.OUTCLK_2, 5, 'ns').start())
            cocotb.start_soon(Clock(self._core.clk_gen_i.OUTCLK_3, 10, 'ns').start())

        pcie_clks = SignalProxy(self._core.pcie_i.pcie_core_i.pcie_hip_clk)

        for i in range(len(pcie_clks)):
            if self._core.pcie_i.pcie_core_i.ENDPOINT_TYPE.value.decode() == "P_TILE":
                # This is default value in IP core for g4_pld_clkfreq_user_hwctl
                period = 2.5
            else:
                period = 4

            cocotb.start_soon(Clock(pcie_clks[i], period, 'ns', impl="py").start())

        for eth_core in self._core.network_mod_i.eth_core_g if hasattr(self._core.network_mod_i, 'eth_core_g') else []:
            if hasattr(eth_core.network_mod_core_i, 'cmac_clk_322m'):
                cocotb.start_soon(Clock(eth_core.network_mod_core_i.cmac_clk_322m, 3106, 'ps').start())
            if hasattr(eth_core.network_mod_core_i, 'etile_clk_out'):
                cocotb.start_soon(Clock(eth_core.network_mod_core_i.etile_clk_out, 2482, 'ps').start())
            if hasattr(eth_core.network_mod_core_i, 'ftile_clk_out'):
                cocotb.start_soon(Clock(eth_core.network_mod_core_i.ftile_clk_out, 2482, 'ps').start())

    def _init_pcie(self):
        try:
            self._core = NFBDevice.core_instance_from_top(self._dut)
        except Exception:
            # No fpga_common instance in card, try fpga_common directly
            self._core = self._dut

        try:
            pkg_name = "ndk_fpga_top_pkg"
            _pkg = simulator.get_root_handle(pkg_name)
            pkg = cocotb.handle.HierarchyObject(_pkg, pkg_name)
            self._card_name = pkg.CARD_NAME.value.decode()
        except Exception:
            # Workardound for nvc
            self._card_name = self._core.BOARD.value.decode()

        pcie_i = self._core.pcie_i.pcie_core_i
        self.mi = []
        self.pcie_req = []

        pcie_clk = SignalProxy(pcie_i.pcie_clk)

        for i in range(len(pcie_clk)):
            clk = pcie_clk[i]

            if hasattr(pcie_i, "pcie_cq_axi_data"):
                cq  = Axi4sPcieDriverMaster(pcie_i, "pcie_cq_axi", clk, array_idx=i)
                cc  = Axi4sPcieDriverSlave(pcie_i, "pcie_cc_axi", clk, array_idx=i)
                ccm = Axi4StreamV(pcie_i, "pcie_cc_axi", clk, 0, aux_signals=True, array_idx=i)

                rq  = Axi4sPcieDriverSlave(pcie_i, "pcie_rq_axi", clk, array_idx=i)
                rc  = Axi4sPcieDriverMaster(pcie_i, "pcie_rc_axi", clk, array_idx=i)
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

                if hasattr(pcie_i, "pcie_dcrdt_up_init"): # R-TILE
                    hcrdt_rx = AvstCreditorRX(pcie_i, "pcie_hcrdt_dw", clk, array_idx=i)
                    dcrdt_rx = AvstCreditorRX(pcie_i, "pcie_dcrdt_dw", clk, array_idx=i)
                    cq_rc_drv = AvstCreditRequester(cq_rc_drv, hcrdt_rx, dcrdt_rx)

                    hcrdt_tx = AvstCreditorTX(pcie_i, "pcie_hcrdt_up", clk, array_idx=i, credits=[0, 32, 32])
                    dcrdt_tx = AvstCreditorTX(pcie_i, "pcie_dcrdt_up", clk, array_idx=i, credits=[0, 1024, 1024])
                    cc_mon = AvstCreditReceiver(cc_mon, hcrdt_tx, dcrdt_tx)
                    rq_mon = AvstCreditReceiver(rq_mon, hcrdt_tx, dcrdt_tx)

                req = AvstRequester(self.ram, cc_rq_drv, cq_rc_drv, rq_mon)
                mi = AvstCompleter(cq_rc_drv, cc_rq_drv, cc_mon)
                self.mi.append(mi)
                self.pcie_req.append(req)

        self._eth_rx_driver = []
        self._eth_tx_monitor = []

        # iterating over ports
        for i, eth_core in enumerate(self._core.network_mod_i.eth_core_g if hasattr(self._core.network_mod_i, 'eth_core_g') else []):
            eth_core.network_mod_core_i.TX_LINK_UP.value = Force(1)
            eth_core.network_mod_core_i.RX_LINK_UP.value = Force(1)

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

            if hasattr(eth_core.network_mod_core_i, 'ftile_tx_mac_ready'):
                eth_core.network_mod_core_i.ftile_tx_mac_ready.value = 1

                # iterating over channels
                for j in range(len(eth_core.network_mod_core_i.ftile_tx_adapt_valid)):
                    tx_monitor = MAC_Segmented_TX_Monitor(eth_core.network_mod_core_i, "ftile_tx_adapt", eth_core.network_mod_core_i.ftile_clk_out, array_idx=j)
                    self._eth_tx_monitor.append(tx_monitor)
                for j in range(len(eth_core.network_mod_core_i.ftile_rx_mac_valid)):
                    rx_driver = MAC_Segmented_RX_Driver(eth_core.network_mod_core_i, "ftile_rx_mac", eth_core.network_mod_core_i.ftile_clk_out, array_idx=j)
                    self._eth_rx_driver.append(rx_driver)

        self.dtb = None

    async def _reset(self, time=40, units="ns"):
        t = Timer(time, units)
        pcie_i = self._core.pcie_i.pcie_core_i

        if hasattr(pcie_i, 'pcie_hip_rst'):
            rsts = pcie_i.pcie_hip_rst
            rsts.value = "1" * len(rsts)
            await t
            rsts.value = "0" * len(rsts)

            # FIXME: some strange loopback on ALVEO_U200
            if self._core.USE_PCIE_CLK.value == 1:
                await FallingEdge(self._core.global_reset)

        elif hasattr(pcie_i, 'pcie_reset_status_n'):
            rsts = pcie_i.pcie_reset_status_n
            pcie_i.pcie_reset_status_n.value = "0" * len(rsts)
            await t
            pcie_i.pcie_reset_status_n.value = "1" * len(rsts)

        else:
            raise NotImplementedError("Unknown signals for PCI/device reset")

        rst_pci = SignalProxy(self._core.rst_pci)
        i = len(rst_pci) - 1

        if rst_pci[i].value == 1:
            await FallingEdge(rst_pci[i])

    async def _pcie_cfg_ext_reg_access(self, addr, index=0, fn=0, sync=True, data=None):
        pcie_i = self._core.pcie_i.pcie_core_i
        clk = SignalProxy(pcie_i.pcie_hip_clk, index)

        if sync:
            await RisingEdge(clk)

        pcie_i.cfg_ext_function[index].value = fn
        pcie_i.cfg_ext_register[index].value = addr >> 2
        pcie_i.cfg_ext_read[index].value = 1 if data is None else 0
        pcie_i.cfg_ext_write[index].value = 0 if data is None else 1
        if data:
            pcie_i.cfg_ext_write_data[index].value = data
        await RisingEdge(clk)
        pcie_i.cfg_ext_read[index].value = 0
        pcie_i.cfg_ext_write[index].value = 0
        if data is None:
            return pcie_i.cfg_ext_read_data[index].value.integer

    async def _pcie_cfg_ext_reg_read(self, addr, index=0, fn=0, sync=True):
        return await self._pcie_cfg_ext_reg_access(addr, index, fn, sync)

    async def _pcie_cfg_ext_reg_write(self, addr, data, index=0, fn=0, sync=True):
        await self._pcie_cfg_ext_reg_access(addr, index, fn, sync, data)

    async def _read_dtb_raw(self, cap_dtb=0x480):
        dtb_length = await self._pcie_cfg_ext_reg_read(cap_dtb + 0x0c)
        data = []
        for i in range(dtb_length // 4):
            await self._pcie_cfg_ext_reg_write(cap_dtb + 0x10, i, sync=False)
            data.append(await self._pcie_cfg_ext_reg_read(cap_dtb + 0x14, sync=True))

        return bytes(sum([[(x >> 0) & 0xFF, (x >> 8) & 0xFF, (x >> 16) & 0xFF, (x >> 24) & 0xFF] for x in data], []))
