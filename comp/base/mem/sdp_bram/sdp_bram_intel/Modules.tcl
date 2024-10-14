# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set MOD "$MOD $ENTITY_BASE/sdp_bram_intel_ent.vhd"

if {"altera" in $PLATFORM_TAGS} {
    set MOD "$MOD $ENTITY_BASE/sdp_bram_intel.vhd"
} else {
    set MOD "$MOD $ENTITY_BASE/sdp_bram_intel_empty.vhd"
}
