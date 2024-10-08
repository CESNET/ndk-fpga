# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2012 CESNET
# Author: Pavel Benacek <benacek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set ASFIFO_BASE      "$OFM_PATH/comp/base/fifo/asfifo_bram"
set MATH_PKG_BASE    "$OFM_PATH/comp/base/pkg"

# Packages
set PACKAGES         "$PACKAGES $MATH_PKG_BASE/math_pack.vhd"

# Subcomponents
set COMPONENTS [list [list "GEN_OR" $OFM_PATH/comp/base/logic/or "FULL"] \
                     [list "ASFIFO_BRAM"    $ASFIFO_BASE     "FULL"]]

# Entities
set MOD "$MOD $ENTITY_BASE/asfifo_ent.vhd"
set MOD "$MOD $ENTITY_BASE/asfifo_arch.vhd"
