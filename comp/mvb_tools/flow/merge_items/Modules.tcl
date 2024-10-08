# Modules.tcl: Script to compile single module
# Copyright (C) 2022 CESNET
# Author: Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set FIFOX_MULTI_BASE "$OFM_PATH/comp/base/fifo/fifox_multi"
set MVB_FIFOX_BASE   "$OFM_PATH/comp/mvb_tools/storage/fifox"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "FIFOX_MULTI" $FIFOX_MULTI_BASE "FULL" ]
lappend COMPONENTS [ list "MVB_FIFOX"   $MVB_FIFOX_BASE   "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/merge_items.vhd"
