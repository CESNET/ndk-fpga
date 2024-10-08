# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2014 CESNET
# Author: Jakub Cabal <jakubcabal@gmail.com>
#
# SPDX-License-Identifier: BSD-3-Clause

set ASFIFO_BASE     "$OFM_PATH/comp/base/fifo/asfifo"
set MATH_PKG_BASE   "$OFM_PATH/comp/base/pkg"

# Packages
set PACKAGES        "$PACKAGES $MATH_PKG_BASE/math_pack.vhd"

# Subcomponents
set COMPONENTS [list [list "GEN_OR" $OFM_PATH/comp/base/logic/or "FULL" ] \
                     [list "ASFIFO" $ASFIFO_BASE             "FULL"]]

# Entities
set MOD "$MOD $ENTITY_BASE/fl_asfifo_lut.vhd"
