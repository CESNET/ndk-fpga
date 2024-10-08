# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
# Author: Martinek Tomas <martinek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components
set PKG_BASE "$OFM_PATH/comp/base/pkg"
set COMPONENTS [list [ list "PKG" $PKG_BASE "MATH"] ]

set MOD "$MOD $ENTITY_BASE/dec1fn.vhd"
set MOD "$MOD $ENTITY_BASE/dec1fn_enable.vhd"
set MOD "$MOD $ENTITY_BASE/dec1fn2b.vhd"
