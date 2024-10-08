# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set GEN_MUX_BASE   "$OFM_PATH/comp/base/logic/mux"
set FIRST_ONE_BASE "$OFM_PATH/comp/base/logic/first_one"

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
   [list "GEN_MUX_ONEHOT" $GEN_MUX_BASE   "FULL" ] \
   [list "FIRST_ONE"      $FIRST_ONE_BASE "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mvb_realign_eof2sof.vhd"
