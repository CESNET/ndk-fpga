# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE    "$OFM_PATH/comp/base/pkg"
set LUTRAM_BASE "$OFM_PATH/comp/base/mem/gen_lutram"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"

set COMPONENTS [list [list "GEN_LUTRAM" $LUTRAM_BASE "FULL"]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/sp_distmem.vhd"
set MOD "$MOD $ENTITY_BASE/dp_distmem.vhd"
set MOD "$MOD $ENTITY_BASE/qp_distmem.vhd"
set MOD "$MOD $ENTITY_BASE/sdp_distmem.vhd"
