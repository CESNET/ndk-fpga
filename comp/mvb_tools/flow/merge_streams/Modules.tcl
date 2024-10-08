# Modules.tcl: Script to compile single module
# Copyright (C) 2023 CESNET
# Author: Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SHAKEDOWN_BASE "$OFM_PATH/comp/mvb_tools/flow/shakedown"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "SHAKEDOWN" $SHAKEDOWN_BASE "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/merge_streams.vhd"
