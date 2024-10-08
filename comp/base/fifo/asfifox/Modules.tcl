# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set PKG_BASE                 "$OFM_PATH/comp/base/pkg"
set SDP_BRAM_BASE            "$OFM_PATH/comp/base/mem/sdp_bram"
set GEN_LUTRAM_BASE          "$OFM_PATH/comp/base/mem/gen_lutram"
set ASYNC_OPEN_LOOP_SMD_BASE "$OFM_PATH/comp/base/async/open_loop_smd"
set ASYNC_RESET_BASE         "$OFM_PATH/comp/base/async/reset"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"

# Components
lappend COMPONENTS [ list "SDP_BRAM_BEHAV"      $SDP_BRAM_BASE            "FULL" ]
lappend COMPONENTS [ list "GEN_LUTRAM"          $GEN_LUTRAM_BASE          "FULL" ]
lappend COMPONENTS [ list "ASYNC_OPEN_LOOP_SMD" $ASYNC_OPEN_LOOP_SMD_BASE "FULL" ]
lappend COMPONENTS [ list "ASYNC_RESET"         $ASYNC_RESET_BASE         "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/asfifox.vhd"
