# Modules.tcl: script to compile single module
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Component paths
set DEC1FN_BASE  "$OFM_PATH/comp/base/logic/dec1fn"
set BIN2HOT_BASE "$OFM_PATH/comp/base/logic/bin2hot"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
#lappend COMPONENTS [ list "DEC1FN"  $DEC1FN_BASE  "FULL" ]
#lappend COMPONENTS [ list "BIN2HOT" $BIN2HOT_BASE "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/mfb_frame_trimmer.vhd"
