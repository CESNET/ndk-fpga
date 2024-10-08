# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE     "$OFM_PATH/comp/base/pkg"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
    [ list "GEN_MUX_PIPED"             "$OFM_PATH/comp/base/logic/mux"               "FULL" ] \
    [ list "BARREL_SHIFTER_GEN_PIPED"  "$OFM_PATH/comp/base/logic/barrel_shifter"    "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/crossbar.vhd"

lappend SRCS(CONSTR_QUARTUS) [list $ENTITY_BASE/crossbar.sdc SDC_ENTITY_FILE crossbar]
