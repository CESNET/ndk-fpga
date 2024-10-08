# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set GEN_LUTRAM_BASE    "$OFM_PATH/comp/base/mem/gen_lutram"
set SDP_BRAM_BASE      "$OFM_PATH/comp/base/mem/sdp_bram"
set SDP_URAM_BASE      "$OFM_PATH/comp/base/mem/sdp_uram_xilinx"

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
   [ list "SDP_BRAM_BEHAV"      $SDP_BRAM_BASE     "FULL" ] \
   [ list "GEN_LUTRAM"          $GEN_LUTRAM_BASE   "FULL" ] \
   [ list "SDP_URAM"            $SDP_URAM_BASE     "FULL" ]
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/sdp_memx.vhd"
