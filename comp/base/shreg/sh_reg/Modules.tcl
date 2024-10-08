# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
# Author: Martinek Tomas <martinek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

#here used to be sh_reg, sh_reg_emem. please now use ../sh_reg_base/sh_reg_base_(dynamic|static)
#set MOD "$MOD $ENTITY_BASE/sh_reg_elem.vhd"
#set MOD "$MOD $ENTITY_BASE/sh_reg.vhd"

set MOD "$MOD $ENTITY_BASE/sh_reg_bus.vhd"


set SH_REG_BASE "$ENTITY_BASE/../sh_reg_base"
set COMPONENTS [list \
   [list "SH_REG_BASE_STATIC"  $SH_REG_BASE  "FULL"] \
]
