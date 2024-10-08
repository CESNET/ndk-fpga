# Modules.tcl: script to compile single module
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Component paths
set MVB_ASFIFOX_BASE  "$OFM_PATH/comp/mvb_tools/storage/asfifox"
set MFB_ASFIFOX_BASE  "$OFM_PATH/comp/mfb_tools/storage/asfifox"
set MFB_DROPPER_BASE  "$OFM_PATH/comp/mfb_tools/flow/dropper"
set METADATA_INS_BASE "$OFM_PATH/comp/mfb_tools/flow/metadata_insertor"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "MVB_ASFIFOX"  $MVB_ASFIFOX_BASE  "FULL" ]
lappend COMPONENTS [ list "MFB_ASFIFOX"  $MFB_ASFIFOX_BASE  "FULL" ]
lappend COMPONENTS [ list "MFB_DROPPER"  $MFB_DROPPER_BASE  "FULL" ]
lappend COMPONENTS [ list "METADATA_INS" $METADATA_INS_BASE "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/pd_asfifo_simple.vhd"
