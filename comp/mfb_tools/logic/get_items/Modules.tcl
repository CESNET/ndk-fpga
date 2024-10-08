# Modules.tcl: Components include script
# Copyright (C) 2017 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set GEN_MUX_BASE "$OFM_PATH/comp/base/logic/mux"

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
    [list "GEN_MUX" $GEN_MUX_BASE "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mfb_get_items.vhd"
