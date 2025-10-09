# qsfp.xdc
# Copyright (C) 2024 DynaNIC Semiconductors, Ltd.
# Author(s): David Beneš <benes@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

#####################################################################################
# QSFP Clock
#####################################################################################
set_property PACKAGE_PIN N32 [get_ports {QSFP0_REFCLK_P}]
set_property PACKAGE_PIN N33 [get_ports {QSFP0_REFCLK_N}]

set_property PACKAGE_PIN U32 [get_ports {QSFP1_REFCLK_P}]
set_property PACKAGE_PIN U33 [get_ports {QSFP1_REFCLK_N}]

create_clock -period 6.4 [get_ports {QSFP0_REFCLK_P}]
create_clock -period 6.4 [get_ports {QSFP1_REFCLK_P}]

#####################################################################################
# QSFP Data (Up to 200Gbps) - Line rate is 25Gbps
# Connector 1
#####################################################################################
set_property PACKAGE_PIN G41 [get_ports {QSFP0_RX_P[0]}]
set_property PACKAGE_PIN F39 [get_ports {QSFP0_RX_P[1]}]
set_property PACKAGE_PIN E41 [get_ports {QSFP0_RX_P[2]}]
set_property PACKAGE_PIN D39 [get_ports {QSFP0_RX_P[3]}]
# set_property PACKAGE_PIN L41 [get_ports {QSFP0_RX_P[4]}]
# set_property PACKAGE_PIN K39 [get_ports {QSFP0_RX_P[5]}]
# set_property PACKAGE_PIN J41 [get_ports {QSFP0_RX_P[6]}]
# set_property PACKAGE_PIN H39 [get_ports {QSFP0_RX_P[7]}]

set_property PACKAGE_PIN H34 [get_ports {QSFP0_TX_P[0]}]
set_property PACKAGE_PIN G36 [get_ports {QSFP0_TX_P[1]}]
set_property PACKAGE_PIN F34 [get_ports {QSFP0_TX_P[2]}]
set_property PACKAGE_PIN E36 [get_ports {QSFP0_TX_P[3]}]
# set_property PACKAGE_PIN M34 [get_ports {QSFP0_TX_P[4]}]
# set_property PACKAGE_PIN L36 [get_ports {QSFP0_TX_P[5]}]
# set_property PACKAGE_PIN K34 [get_ports {QSFP0_TX_P[6]}]
# set_property PACKAGE_PIN J36 [get_ports {QSFP0_TX_P[7]}]

set_property PACKAGE_PIN G42 [get_ports {QSFP0_RX_N[0]}]
set_property PACKAGE_PIN F40 [get_ports {QSFP0_RX_N[1]}]
set_property PACKAGE_PIN E42 [get_ports {QSFP0_RX_N[2]}]
set_property PACKAGE_PIN D40 [get_ports {QSFP0_RX_N[3]}]
# set_property PACKAGE_PIN L42 [get_ports {QSFP0_RX_N[4]}]
# set_property PACKAGE_PIN K40 [get_ports {QSFP0_RX_N[5]}]
# set_property PACKAGE_PIN J42 [get_ports {QSFP0_RX_N[6]}]
# set_property PACKAGE_PIN H40 [get_ports {QSFP0_RX_N[7]}]

set_property PACKAGE_PIN H35 [get_ports {QSFP0_TX_N[0]}]
set_property PACKAGE_PIN G37 [get_ports {QSFP0_TX_N[1]}]
set_property PACKAGE_PIN F35 [get_ports {QSFP0_TX_N[2]}]
set_property PACKAGE_PIN E37 [get_ports {QSFP0_TX_N[3]}]
# set_property PACKAGE_PIN M35 [get_ports {QSFP0_TX_N[4]}]
# set_property PACKAGE_PIN L37 [get_ports {QSFP0_TX_N[5]}]
# set_property PACKAGE_PIN K35 [get_ports {QSFP0_TX_N[6]}]
# set_property PACKAGE_PIN J37 [get_ports {QSFP0_TX_N[7]}]

#####################################################################################
# QSFP Data (Up to 200Gbps) - Line rate is 25Gbps
# Connector 2
#####################################################################################
set_property PACKAGE_PIN R41 [get_ports {QSFP1_RX_P[0]}]
set_property PACKAGE_PIN P39 [get_ports {QSFP1_RX_P[1]}]
set_property PACKAGE_PIN N41 [get_ports {QSFP1_RX_P[2]}]
set_property PACKAGE_PIN M39 [get_ports {QSFP1_RX_P[3]}]
# set_property PACKAGE_PIN W41 [get_ports {QSFP1_RX_P[4]}]
# set_property PACKAGE_PIN V39 [get_ports {QSFP1_RX_P[5]}]
# set_property PACKAGE_PIN U41 [get_ports {QSFP1_RX_P[6]}]
# set_property PACKAGE_PIN T39 [get_ports {QSFP1_RX_P[7]}]

set_property PACKAGE_PIN T34 [get_ports {QSFP1_TX_P[0]}]
set_property PACKAGE_PIN R36 [get_ports {QSFP1_TX_P[1]}]
set_property PACKAGE_PIN P34 [get_ports {QSFP1_TX_P[2]}]
set_property PACKAGE_PIN N36 [get_ports {QSFP1_TX_P[3]}]
# set_property PACKAGE_PIN Y34 [get_ports {QSFP1_TX_P[4]}]
# set_property PACKAGE_PIN W36 [get_ports {QSFP1_TX_P[5]}]
# set_property PACKAGE_PIN V34 [get_ports {QSFP1_TX_P[6]}]
# set_property PACKAGE_PIN U36 [get_ports {QSFP1_TX_P[7]}]

set_property PACKAGE_PIN R42 [get_ports {QSFP1_RX_N[0]}]
set_property PACKAGE_PIN P40 [get_ports {QSFP1_RX_N[1]}]
set_property PACKAGE_PIN N42 [get_ports {QSFP1_RX_N[2]}]
set_property PACKAGE_PIN M40 [get_ports {QSFP1_RX_N[3]}]
# set_property PACKAGE_PIN W42 [get_ports {QSFP1_RX_N[4]}]
# set_property PACKAGE_PIN V40 [get_ports {QSFP1_RX_N[5]}]
# set_property PACKAGE_PIN U42 [get_ports {QSFP1_RX_N[6]}]
# set_property PACKAGE_PIN T40 [get_ports {QSFP1_RX_N[7]}]

set_property PACKAGE_PIN T35 [get_ports {QSFP1_TX_N[0]}]
set_property PACKAGE_PIN R37 [get_ports {QSFP1_TX_N[1]}]
set_property PACKAGE_PIN P35 [get_ports {QSFP1_TX_N[2]}]
set_property PACKAGE_PIN N37 [get_ports {QSFP1_TX_N[3]}]
# set_property PACKAGE_PIN Y35 [get_ports {QSFP1_TX_N[4]}]
# set_property PACKAGE_PIN W37 [get_ports {QSFP1_TX_N[5]}]
# set_property PACKAGE_PIN V35 [get_ports {QSFP1_TX_N[6]}]
# set_property PACKAGE_PIN U37 [get_ports {QSFP1_TX_N[7]}]

#####################################################################################
# QSFP Control signals GPIO Constraints
#####################################################################################
set_property PACKAGE_PIN B8 [get_ports {QSFP0_MODSEL_N}]
set_property PACKAGE_PIN A8 [get_ports {QSFP0_RESET_N}]
set_property PACKAGE_PIN J9 [get_ports {QSFP0_LPMODE}]
set_property PACKAGE_PIN H9 [get_ports {QSFP0_INT_N}]
set_property PACKAGE_PIN C8 [get_ports {QSFP0_MODPRS_N}]

set_property PACKAGE_PIN D8 [get_ports {QSFP1_MODSEL_N}]
set_property PACKAGE_PIN E9 [get_ports {QSFP1_RESET_N}]
set_property PACKAGE_PIN F9 [get_ports {QSFP1_LPMODE}]
set_property PACKAGE_PIN D9 [get_ports {QSFP1_INT_N}]
set_property PACKAGE_PIN C9 [get_ports {QSFP1_MODPRS_N}]

# set_property PACKAGE_PIN E6 [get_ports {QSFP2_MODSEL_N}]
# set_property PACKAGE_PIN D6 [get_ports {QSFP2_RESET_N}]
# set_property PACKAGE_PIN F6 [get_ports {QSFP2_LPMODE}]
# set_property PACKAGE_PIN G6 [get_ports {QSFP2_INT_N}]
# set_property PACKAGE_PIN A5 [get_ports {QSFP2_MODPRS_N}]

set_property IOSTANDARD LVCMOS33 [get_ports {QSFP0_MODSEL_N}]
set_property IOSTANDARD LVCMOS33 [get_ports {QSFP0_RESET_N}]
set_property IOSTANDARD LVCMOS33 [get_ports {QSFP0_LPMODE}]
set_property IOSTANDARD LVCMOS33 [get_ports {QSFP0_INT_N}]
set_property IOSTANDARD LVCMOS33 [get_ports {QSFP0_MODPRS_N}]

set_property IOSTANDARD LVCMOS33 [get_ports {QSFP1_MODSEL_N}]
set_property IOSTANDARD LVCMOS33 [get_ports {QSFP1_RESET_N}]
set_property IOSTANDARD LVCMOS33 [get_ports {QSFP1_LPMODE}]
set_property IOSTANDARD LVCMOS33 [get_ports {QSFP1_INT_N}]
set_property IOSTANDARD LVCMOS33 [get_ports {QSFP1_MODPRS_N}]

# set_property IOSTANDARD LVCMOS33 [get_ports {QSFP2_MODSEL_N}]
# set_property IOSTANDARD LVCMOS33 [get_ports {QSFP2_RESET_N}]
# set_property IOSTANDARD LVCMOS33 [get_ports {QSFP2_LPMODE}]
# set_property IOSTANDARD LVCMOS33 [get_ports {QSFP2_INT_N}]
# set_property IOSTANDARD LVCMOS33 [get_ports {QSFP2_MODPRS_N}]
