# Modules.tcl: Components include script
# Copyright (C) 2017 CESNET
# Author(s): Jakub Cabal <xcabal05@stud.feec.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set GEN_MUX_BASE "$OFM_PATH/comp/base/logic/mux"

set PACKAGES     "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mvb_reordering_logic.vhd"
set MOD "$MOD $ENTITY_BASE/mvb_reordering.vhd"

set COMPONENTS [list \
   [list "GEN_MUX" $GEN_MUX_BASE "FULL" ] \
]

