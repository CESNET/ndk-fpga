# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
# Author: Martinek Tomas <martinek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

if { $ARCHGRP == "MATH" } {
   set MOD "$MOD $ENTITY_BASE/math_pack.vhd"
}

if { $ARCHGRP == "TYPE" } {
   set MOD "$MOD $ENTITY_BASE/math_pack.vhd"
   set MOD "$MOD $ENTITY_BASE/type_pack.vhd"
}

if { $ARCHGRP == "DMA_PKG"} {
   set MOD "$MOD $ENTITY_BASE/dma_bus_pack.vhd"
}

if {$ARCHGRP == "SV_DMA_PKG"} {
   set MOD "$MOD $ENTITY_BASE/dma_bus_pack.sv"
}

if { $ARCHGRP == "ETH_HDR_PKG"} {
   set MOD "$MOD $ENTITY_BASE/eth_hdr_pack.vhd"
}

if { $ARCHGRP == "PCIE_META_PKG"} {
   set MOD "$MOD $ENTITY_BASE/pcie_meta_pack.vhd"
}
