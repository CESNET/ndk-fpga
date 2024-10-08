# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set MOD "$MOD $ENTITY_BASE/altdpram_wrap_ent.vhd"

global SYNTH_FLAGS
if { [info exists SYNTH_FLAGS(TOOL)] && $SYNTH_FLAGS(TOOL) != "quartus" } {
    set MOD "$MOD $ENTITY_BASE/altdpram_wrap_empty.vhd"
} else {
    set MOD "$MOD $ENTITY_BASE/altdpram_wrap.vhd"
}
