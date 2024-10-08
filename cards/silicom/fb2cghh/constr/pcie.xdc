# pcie.xdc
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): David Beneš <benes.david2000@seznam.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set_property PACKAGE_PIN G1      [get_ports {PCIE_SYSRST_N}]
set_property IOSTANDARD LVCMOS33 [get_ports {PCIE_SYSRST_N}]

set_property PACKAGE_PIN AL16    [get_ports {PCIE_RST1V2_N}]
set_property IOSTANDARD LVCMOS12 [get_ports {PCIE_RST1V2_N}]

set_property PACKAGE_PIN AN10    [get_ports {PCIE_SYSCLK_P}] 
set_property PACKAGE_PIN AN9     [get_ports {PCIE_SYSCLK_N}] 

create_clock -period 10.000 -name pcie_clk_p -waveform {0.000 5.000} [get_ports PCIE_SYSCLK_P]
