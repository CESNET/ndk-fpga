# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE  "$OFM_PATH/comp/base/pkg"

# Paths to components
set DEC1FN_BASE        "$OFM_PATH/comp/base/logic/dec1fn"
set FIRST_ONE_BASE     "$OFM_PATH/comp/base/logic/first_one"
set GEN_MUX_PIPED_BASE "$OFM_PATH/comp/base/logic/mux"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
   [ list "DEC1FN"        $DEC1FN_BASE        "FULL" ] \
   [ list "FIRST_ONE"     $FIRST_ONE_BASE     "FULL" ] \
   [ list "GEN_MUX_PIPED" $GEN_MUX_PIPED_BASE "FULL" ]
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/gen_reg_array.vhd"
