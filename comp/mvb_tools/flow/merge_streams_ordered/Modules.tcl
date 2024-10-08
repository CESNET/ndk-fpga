# Modules.tcl: Script to compile single module
# Copyright (C) 2024 CESNET
# Author: Oliver Gurka <oliver.gurka@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set FIFOX_MULTI_BASE    "$OFM_PATH/comp/base/fifo/fifox_multi"
set SHAKEDOWN_BASE      "$OFM_PATH/comp/mvb_tools/flow/merge_n_to_m"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

set SHAKEDOWN_BASE      "$OFM_PATH/comp/mvb_tools/flow/merge_n_to_m"
set MVB_SHAKEDOWN_BASE  "$OFM_PATH/comp/mvb_tools/flow/shakedown"
set FIFOX_MULTI_BASE    "$OFM_PATH/comp/base/fifo/fifox_multi"

# Components
lappend COMPONENTS [list "SHAKEDOWN"        $SHAKEDOWN_BASE     "FULL"]
lappend COMPONENTS [list "FIFOX_MULTI"      $FIFOX_MULTI_BASE   "FULL"]
lappend COMPONENTS [list "MVB_SHAKEDOWN"    $MVB_SHAKEDOWN_BASE "FULL"]

# Files
lappend MOD "$ENTITY_BASE/merge_streams_ordered.vhd"
