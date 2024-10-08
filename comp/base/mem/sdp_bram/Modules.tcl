# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE  "$OFM_PATH/comp/base/pkg"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
   [ list "SDP_BRAM_INTEL"   "$ENTITY_BASE/sdp_bram_intel"  "FULL" ] \
   [ list "SDP_BRAM_XILINX2" "$ENTITY_BASE/sdp_bram_xilinx" "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/sdp_bram_behav.vhd"
set MOD "$MOD $ENTITY_BASE/sdp_bram.vhd"
set MOD "$MOD $ENTITY_BASE/sdp_bram_be.vhd"
