# qsfp.xdc
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# ==============================================================================
# QSFP MISC INTERFACES
# ==============================================================================

set_property PACKAGE_PIN BL13     [get_ports "QSFP_ACT_LED_G[0]"];
set_property PACKAGE_PIN BK14     [get_ports "QSFP_ACT_LED_G[1]"];
set_property PACKAGE_PIN BK11     [get_ports "QSFP_STA_LED_G[0]"];
set_property PACKAGE_PIN BK15     [get_ports "QSFP_STA_LED_G[1]"];
set_property PACKAGE_PIN BJ11     [get_ports "QSFP_STA_LED_Y[0]"];
set_property PACKAGE_PIN BL12     [get_ports "QSFP_STA_LED_Y[1]"];

set_property IOSTANDARD  LVCMOS18 [get_ports "QSFP_ACT_LED_G"];
set_property IOSTANDARD  LVCMOS18 [get_ports "QSFP_STA_LED_G"];
set_property IOSTANDARD  LVCMOS18 [get_ports "QSFP_STA_LED_Y"];

# ==============================================================================
# QSFP HIGH SPEED INTERFACES
# ==============================================================================

set_property package_pin AD42 [get_ports {QSFP0_REFCLK_P}]
set_property package_pin AD43 [get_ports {QSFP0_REFCLK_N}]
create_clock -period 6.206    [get_ports {QSFP0_REFCLK_P}]

set_property package_pin AB42 [get_ports {QSFP1_REFCLK_P}]
set_property package_pin AB43 [get_ports {QSFP1_REFCLK_N}]
create_clock -period 6.206    [get_ports {QSFP1_REFCLK_P}]

set_property PACKAGE_PIN AD51 [get_ports {QSFP0_RX_P[0]}]
set_property PACKAGE_PIN AC53 [get_ports {QSFP0_RX_P[1]}]
set_property PACKAGE_PIN AC49 [get_ports {QSFP0_RX_P[2]}]
set_property PACKAGE_PIN AB51 [get_ports {QSFP0_RX_P[3]}]

set_property PACKAGE_PIN AD52 [get_ports {QSFP0_RX_N[0]}]
set_property PACKAGE_PIN AC54 [get_ports {QSFP0_RX_N[1]}]
set_property PACKAGE_PIN AC50 [get_ports {QSFP0_RX_N[2]}]
set_property PACKAGE_PIN AB52 [get_ports {QSFP0_RX_N[3]}]

set_property PACKAGE_PIN AD46 [get_ports {QSFP0_TX_P[0]}]
set_property PACKAGE_PIN AC44 [get_ports {QSFP0_TX_P[1]}]
set_property PACKAGE_PIN AB46 [get_ports {QSFP0_TX_P[2]}]
set_property PACKAGE_PIN AA48 [get_ports {QSFP0_TX_P[3]}]

set_property PACKAGE_PIN AD47 [get_ports {QSFP0_TX_N[0]}]
set_property PACKAGE_PIN AC45 [get_ports {QSFP0_TX_N[1]}]
set_property PACKAGE_PIN AB47 [get_ports {QSFP0_TX_N[2]}]
set_property PACKAGE_PIN AA49 [get_ports {QSFP0_TX_N[3]}]

set_property PACKAGE_PIN AA53 [get_ports {QSFP1_RX_P[0]}]
set_property PACKAGE_PIN Y51  [get_ports {QSFP1_RX_P[1]}]
set_property PACKAGE_PIN W53  [get_ports {QSFP1_RX_P[2]}]
set_property PACKAGE_PIN V51  [get_ports {QSFP1_RX_P[3]}]

set_property PACKAGE_PIN AA54 [get_ports {QSFP1_RX_N[0]}]
set_property PACKAGE_PIN Y52  [get_ports {QSFP1_RX_N[1]}]
set_property PACKAGE_PIN W54  [get_ports {QSFP1_RX_N[2]}]
set_property PACKAGE_PIN V52  [get_ports {QSFP1_RX_N[3]}]

set_property PACKAGE_PIN AA44 [get_ports {QSFP1_TX_P[0]}]
set_property PACKAGE_PIN Y46  [get_ports {QSFP1_TX_P[1]}]
set_property PACKAGE_PIN W48  [get_ports {QSFP1_TX_P[2]}]
set_property PACKAGE_PIN W44  [get_ports {QSFP1_TX_P[3]}]

set_property PACKAGE_PIN AA45 [get_ports {QSFP1_TX_N[0]}]
set_property PACKAGE_PIN Y47  [get_ports {QSFP1_TX_N[1]}]
set_property PACKAGE_PIN W49  [get_ports {QSFP1_TX_N[2]}]
set_property PACKAGE_PIN W45  [get_ports {QSFP1_TX_N[3]}]
