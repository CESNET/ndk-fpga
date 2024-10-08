# Modules.tcl: script to compile single module
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Component paths
set GEN_MUX_BASE         "$OFM_PATH/comp/base/logic/mux"
set BIN2HOT_BASE         "$OFM_PATH/comp/base/logic/bin2hot"
set FIFOX_MULTI_BASE     "$OFM_PATH/comp/base/fifo/fifox_multi"
set MFB_AUX_SIG_BASE     "$OFM_PATH/comp/mfb_tools/logic/auxiliary_signals"
set MFB_USR_PKT_GEN_BASE "$OFM_PATH/comp/mfb_tools/logic/user_packet_gen"
set MVB_FIFOX_BASE       "$OFM_PATH/comp/mvb_tools/storage/fifox"
set SHAKEDOWN_BASE       "$OFM_PATH/comp/mvb_tools/flow/merge_n_to_m"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "GEN_MUX"         $GEN_MUX_BASE         "FULL" ]
lappend COMPONENTS [ list "BIN2HOT"         $BIN2HOT_BASE         "FULL" ]
lappend COMPONENTS [ list "FIFOX_MULTI"     $FIFOX_MULTI_BASE     "FULL" ]
lappend COMPONENTS [ list "MFB_AUX_SIG"     $MFB_AUX_SIG_BASE     "FULL" ]
lappend COMPONENTS [ list "MFB_USR_PKT_GEN" $MFB_USR_PKT_GEN_BASE "FULL" ]
lappend COMPONENTS [ list "MVB_FIFOX"       $MVB_FIFOX_BASE       "FULL" ]
lappend COMPONENTS [ list "SHAKEDOWN_BASE"  $SHAKEDOWN_BASE       "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/mfb_frame_extender_dm_ctrl.vhd"
lappend MOD "$ENTITY_BASE/mfb_frame_extender_datamover.vhd"
lappend MOD "$ENTITY_BASE/mfb_frame_extender.vhd"
