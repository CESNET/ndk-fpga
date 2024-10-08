# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#


# Paths
set MATH_PKG   "$OFM_PATH/comp/base/pkg"
set LOGIC_BASE "$OFM_PATH/comp/base/logic"

# Packages
set PACKAGES   "$PACKAGES  $MATH_PKG/math_pack.vhd"

# Basic logic components
set MOD "$MOD $LOGIC_BASE/mod/mod.vhd"
set MOD "$MOD $LOGIC_BASE/or/or.vhd"
set MOD "$MOD $LOGIC_BASE/dec1fn/dec1fn_enable.vhd"

# Header insert
set MOD "$MOD $ENTITY_BASE/hins_ent.vhd"

if { $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/hins.vhd"
}

if { $ARCHGRP == "EMPTY" } {
   set MOD "$MOD $ENTITY_BASE/hins_empty.vhd"
}
