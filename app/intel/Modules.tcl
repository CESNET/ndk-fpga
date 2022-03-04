# Modules.tcl: script to compile single module
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Globally defined variables

# Auxiliary paths

# Component paths
set MI_ASYNC_BASE     "$OFM_PATH/comp/mi_tools/async"
set MI_SPLITTER_BASE  "$OFM_PATH/comp/mi_tools/splitter_plus_gen"
set MFB_PIPE_BASE     "$OFM_PATH/comp/mfb_tools/flow/pipe"
set MFB_META_INS_BASE "$OFM_PATH/comp/mfb_tools/flow/metadata_insertor"
set MVB_PIPE_BASE     "$OFM_PATH/comp/mvb_tools/flow/pipe"
set MVB_CHDIST_BASE   "$OFM_PATH/comp/mvb_tools/flow/channel_router"
set MEM_TESTER_BASE   "$OFM_PATH/comp/debug/mem_tester"


# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/eth_hdr_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
   [ list "MI_ASYNC"     $MI_ASYNC_BASE     "FULL" ]\
   [ list "MI_SPLITTER"  $MI_SPLITTER_BASE  "FULL" ]\
   [ list "MFB_META_INS" $MFB_META_INS_BASE "FULL" ]\
   [ list "MFB_PIPE"     $MFB_PIPE_BASE     "FULL" ]\
   [ list "MVB_PIPE"     $MVB_PIPE_BASE     "FULL" ]\
   [ list "MVB_CHDIST"   $MVB_CHDIST_BASE   "FULL" ]\
   [ list "MEM_TESTER"   $MEM_TESTER_BASE   "FULL" ]\
]]

set MOD "$MOD $ENTITY_BASE/app_subcore.vhd"
set MOD "$MOD $ENTITY_BASE/application_core.vhd"
set MOD "$MOD $ENTITY_BASE/DevTree.tcl"
