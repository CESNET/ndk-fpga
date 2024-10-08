# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE         "$OFM_PATH/comp/base/pkg"
set SDP_BRAM_BASE    "$OFM_PATH/comp/base/mem/sdp_bram"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

# Components
lappend COMPONENTS [list   "SDP_BRAM"        $SDP_BRAM_BASE          "FULL"]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/mp_bram.vhd"
