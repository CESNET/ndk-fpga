# qsfp.xdc
# Copyright (C) 2022 CESNET z.s.p.o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# QSFP port 0 - FB4CGG3 only ---------------------------------------------------
set_property PACKAGE_PIN R36 [get_ports {QSFP0_REFCLK_P}]
set_property PACKAGE_PIN R37 [get_ports {QSFP0_REFCLK_N}]
create_clock -name qsfp0_refclk -period 6.206 [get_ports QSFP0_REFCLK_P]

set_property PACKAGE_PIN N40 [get_ports {QSFP0_TX_P[0]}]
set_property PACKAGE_PIN N41 [get_ports {QSFP0_TX_N[0]}]
set_property PACKAGE_PIN N45 [get_ports {QSFP0_RX_P[0]}]
set_property PACKAGE_PIN N46 [get_ports {QSFP0_RX_N[0]}]

set_property PACKAGE_PIN M38 [get_ports {QSFP0_TX_P[1]}]
set_property PACKAGE_PIN M39 [get_ports {QSFP0_TX_N[1]}]
set_property PACKAGE_PIN M43 [get_ports {QSFP0_RX_P[1]}]
set_property PACKAGE_PIN M44 [get_ports {QSFP0_RX_N[1]}]

set_property PACKAGE_PIN L40 [get_ports {QSFP0_TX_P[2]}]
set_property PACKAGE_PIN L41 [get_ports {QSFP0_TX_N[2]}]
set_property PACKAGE_PIN L45 [get_ports {QSFP0_RX_P[2]}]
set_property PACKAGE_PIN L46 [get_ports {QSFP0_RX_N[2]}]

set_property PACKAGE_PIN J40 [get_ports {QSFP0_TX_P[3]}]
set_property PACKAGE_PIN J41 [get_ports {QSFP0_TX_N[3]}]
set_property PACKAGE_PIN K43 [get_ports {QSFP0_RX_P[3]}]
set_property PACKAGE_PIN K44 [get_ports {QSFP0_RX_N[3]}]

# QSFP port 1 - FB4CGG3 only ---------------------------------------------------
set_property PACKAGE_PIN AC36 [get_ports {QSFP1_REFCLK_P}] 
set_property PACKAGE_PIN AC37 [get_ports {QSFP1_REFCLK_N}] 
create_clock -name qsfp1_refclk -period 6.206 [get_ports QSFP1_REFCLK_P]

set_property PACKAGE_PIN AA40 [get_ports {QSFP1_TX_P[0]}]
set_property PACKAGE_PIN AA41 [get_ports {QSFP1_TX_N[0]}]
set_property PACKAGE_PIN AA45 [get_ports {QSFP1_RX_P[0]}]
set_property PACKAGE_PIN AA46 [get_ports {QSFP1_RX_N[0]}]

set_property PACKAGE_PIN Y38 [get_ports {QSFP1_TX_P[1]}]
set_property PACKAGE_PIN Y39 [get_ports {QSFP1_TX_N[1]}]
set_property PACKAGE_PIN Y43 [get_ports {QSFP1_RX_P[1]}]
set_property PACKAGE_PIN Y44 [get_ports {QSFP1_RX_N[1]}]

set_property PACKAGE_PIN W40 [get_ports {QSFP1_TX_P[2]}]
set_property PACKAGE_PIN W41 [get_ports {QSFP1_TX_N[2]}]
set_property PACKAGE_PIN W45 [get_ports {QSFP1_RX_P[2]}]
set_property PACKAGE_PIN W46 [get_ports {QSFP1_RX_N[2]}]

set_property PACKAGE_PIN V38 [get_ports {QSFP1_TX_P[3]}]
set_property PACKAGE_PIN V39 [get_ports {QSFP1_TX_N[3]}]
set_property PACKAGE_PIN V43 [get_ports {QSFP1_RX_P[3]}]
set_property PACKAGE_PIN V44 [get_ports {QSFP1_RX_N[3]}]

# QSFP port 2 - FB4CGG3/FB2CGG3 ------------------------------------------------
set_property PACKAGE_PIN AL36 [get_ports {QSFP2_REFCLK_P}]
set_property PACKAGE_PIN AL37 [get_ports {QSFP2_REFCLK_N}]
create_clock -name qsfp2_refclk -period 6.206 [get_ports QSFP2_REFCLK_P]

set_property PACKAGE_PIN AJ40 [get_ports {QSFP2_TX_P[0]}]
set_property PACKAGE_PIN AJ41 [get_ports {QSFP2_TX_N[0]}]
set_property PACKAGE_PIN AJ45 [get_ports {QSFP2_RX_P[0]}]
set_property PACKAGE_PIN AJ46 [get_ports {QSFP2_RX_N[0]}]

set_property PACKAGE_PIN AH38 [get_ports {QSFP2_TX_P[1]}]
set_property PACKAGE_PIN AH39 [get_ports {QSFP2_TX_N[1]}]
set_property PACKAGE_PIN AH43 [get_ports {QSFP2_RX_P[1]}]
set_property PACKAGE_PIN AH44 [get_ports {QSFP2_RX_N[1]}]

set_property PACKAGE_PIN AG40 [get_ports {QSFP2_TX_P[2]}]
set_property PACKAGE_PIN AG41 [get_ports {QSFP2_TX_N[2]}]
set_property PACKAGE_PIN AG45 [get_ports {QSFP2_RX_P[2]}]
set_property PACKAGE_PIN AG46 [get_ports {QSFP2_RX_N[2]}]

set_property PACKAGE_PIN AF38 [get_ports {QSFP2_TX_P[3]}]
set_property PACKAGE_PIN AF39 [get_ports {QSFP2_TX_N[3]}]
set_property PACKAGE_PIN AF43 [get_ports {QSFP2_RX_P[3]}]
set_property PACKAGE_PIN AF44 [get_ports {QSFP2_RX_N[3]}]

# QSFP port 3 - FB4CGG3/FB2CGG3 ------------------------------------------------
set_property PACKAGE_PIN AU36 [get_ports {QSFP3_REFCLK_P}]
set_property PACKAGE_PIN AU37 [get_ports {QSFP3_REFCLK_N}]
create_clock -name qsfp3_refclk -period 6.206 [get_ports QSFP3_REFCLK_P]

set_property PACKAGE_PIN AU40 [get_ports {QSFP3_TX_P[0]}]
set_property PACKAGE_PIN AU41 [get_ports {QSFP3_TX_N[0]}]
set_property PACKAGE_PIN AU45 [get_ports {QSFP3_RX_P[0]}]
set_property PACKAGE_PIN AU46 [get_ports {QSFP3_RX_N[0]}]

set_property PACKAGE_PIN AT38 [get_ports {QSFP3_TX_P[1]}]
set_property PACKAGE_PIN AT39 [get_ports {QSFP3_TX_N[1]}]
set_property PACKAGE_PIN AT43 [get_ports {QSFP3_RX_P[1]}]
set_property PACKAGE_PIN AT44 [get_ports {QSFP3_RX_N[1]}]

set_property PACKAGE_PIN AR40 [get_ports {QSFP3_TX_P[2]}]
set_property PACKAGE_PIN AR41 [get_ports {QSFP3_TX_N[2]}]
set_property PACKAGE_PIN AR45 [get_ports {QSFP3_RX_P[2]}]
set_property PACKAGE_PIN AR46 [get_ports {QSFP3_RX_N[2]}]

set_property PACKAGE_PIN AP38 [get_ports {QSFP3_TX_P[3]}]
set_property PACKAGE_PIN AP39 [get_ports {QSFP3_TX_N[3]}]
set_property PACKAGE_PIN AP43 [get_ports {QSFP3_RX_P[3]}]
set_property PACKAGE_PIN AP44 [get_ports {QSFP3_RX_N[3]}]

# QSFP misc - FB4CGG3/FB2CGG3 --------------------------------------------------

set_property PACKAGE_PIN BF22 [get_ports {QSFP1_SCL}]       
set_property PACKAGE_PIN BE22 [get_ports {QSFP1_SDA}]       
set_property PACKAGE_PIN BE20 [get_ports {QSFP1_MODPRS_N}]  
set_property PACKAGE_PIN BE21 [get_ports {QSFP1_RESET_N}]   
set_property PACKAGE_PIN BD20 [get_ports {QSFP1_LPMODE}]    
set_property PACKAGE_PIN BD21 [get_ports {QSFP1_INT_N}]

set_property PACKAGE_PIN AR23 [get_ports {QSFP0_SCL}]       
set_property PACKAGE_PIN AT22 [get_ports {QSFP0_SDA}]       
set_property PACKAGE_PIN AR21 [get_ports {QSFP0_MODPRS_N}]  
set_property PACKAGE_PIN AT24 [get_ports {QSFP0_RESET_N}]   
set_property PACKAGE_PIN AU24 [get_ports {QSFP0_LPMODE}]    
set_property PACKAGE_PIN AT23 [get_ports {QSFP0_INT_N}]

set_property PACKAGE_PIN BC23 [get_ports {QSFP2_SCL}]       
set_property PACKAGE_PIN BA23 [get_ports {QSFP2_SDA}]       
set_property PACKAGE_PIN BE23 [get_ports {QSFP2_MODPRS_N}]  
set_property PACKAGE_PIN BF23 [get_ports {QSFP2_RESET_N}]   
set_property PACKAGE_PIN BD23 [get_ports {QSFP2_LPMODE}]    
set_property PACKAGE_PIN BF24 [get_ports {QSFP2_INT_N}]

set_property PACKAGE_PIN BB21 [get_ports {QSFP3_SCL}]       
set_property PACKAGE_PIN BB20 [get_ports {QSFP3_SDA}]       
set_property PACKAGE_PIN BA24 [get_ports {QSFP3_MODPRS_N}]
set_property PACKAGE_PIN BB22 [get_ports {QSFP3_RESET_N}] 
set_property PACKAGE_PIN BC22 [get_ports {QSFP3_LPMODE}]  
set_property PACKAGE_PIN BC21 [get_ports {QSFP3_INT_N}]

set_property IOSTANDARD LVCMOS18 [get_ports {QSFP*_SCL}]
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP*_SDA}]     
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP*_MODPRS_N}]
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP*_RESET_N}] 
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP*_LPMODE}]  
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP*_INT_N}]
