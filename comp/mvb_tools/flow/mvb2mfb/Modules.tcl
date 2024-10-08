# Modules.tcl: Script to compile single module
# Copyright (C) 2023 CESNET
# Author: Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set FIFOX_MULTI_BASE  "$OFM_PATH/comp/base/fifo/fifox_multi"
set GEN_ENC_BASE      "$OFM_PATH/comp/base/logic/enc"
set MFB_RECONFIG_BASE "$OFM_PATH/comp/mfb_tools/flow/reconfigurator"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "FIFOX_MULTI"  $FIFOX_MULTI_BASE  "FULL" ]
lappend COMPONENTS [ list "GEN_ENC"      $GEN_ENC_BASE      "FULL" ]
lappend COMPONENTS [ list "MFB_RECONFIG" $MFB_RECONFIG_BASE "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/mvb2mfb.vhd"
