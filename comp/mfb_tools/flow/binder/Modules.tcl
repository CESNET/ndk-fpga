# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Michal Suchanek <xsucha12@stud.feec.vutbr.cz>
#            Jakub Cabal <cabal@cesnet.cz>
# SPDX-License-Identifier: BSD-3-Clause
#

# Set paths

set PKG_BASE   "$OFM_PATH/comp/base/pkg"
set FIFOX_BASE "$OFM_PATH/comp/base/fifo/fifox"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
   [ list "FIFOX" $FIFOX_BASE "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mfb_binder_mask.vhd"
set MOD "$MOD $ENTITY_BASE/mfb_binder_input.vhd"
set MOD "$MOD $ENTITY_BASE/mfb_binder.vhd"
