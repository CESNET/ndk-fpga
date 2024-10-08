# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set PCIE_AVST2MFB_BASE       "$OFM_PATH/comp/pcie/others/avst2mfb"
set PCIE_MFB2AVST_BASE       "$OFM_PATH/comp/pcie/others/mfb2avst"
set MFB_MERGER_SIMPLE_BASE   "$OFM_PATH/comp/mfb_tools/flow/merger_simple"
set MFB_SPLITTER_SIMPLE_BASE "$OFM_PATH/comp/mfb_tools/flow/splitter_simple"
set MFB_PIPE_BASE            "$OFM_PATH/comp/mfb_tools/flow/pipe"
set PCIE_MFB2AXICQ_BASE      "$OFM_PATH/comp/pcie/others/mfb2axicq"
set PCIE_AXICC2MFB_BASE      "$OFM_PATH/comp/pcie/others/axicc2mfb"
set MFB_FIFOX_BASE           "$OFM_PATH/comp/mfb_tools/storage/fifox"

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set COMPONENTS [concat $COMPONENTS [list \
    [ list "PCIE_AVST2MFB"       $PCIE_AVST2MFB_BASE       "FULL" ] \
    [ list "PCIE_MFB2AVST"       $PCIE_MFB2AVST_BASE       "FULL" ] \
    [ list "PCIE_MFB2AXICQ"      $PCIE_MFB2AXICQ_BASE      "FULL" ] \
    [ list "PCIE_AXICC2MFB"      $PCIE_AXICC2MFB_BASE      "FULL" ] \
    [ list "MFB_MERGER_SIMPLE"   $MFB_MERGER_SIMPLE_BASE   "FULL" ] \
    [ list "MFB_SPLITTER_SIMPLE" $MFB_SPLITTER_SIMPLE_BASE "FULL" ] \
    [ list "MFB_PIPE"            $MFB_PIPE_BASE            "FULL" ] \
    [ list "MFB_FIFOX"           $MFB_FIFOX_BASE           "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/crdt_up.vhd"
set MOD "$MOD $ENTITY_BASE/crdt_down.vhd"
set MOD "$MOD $ENTITY_BASE/connection_block.vhd"
