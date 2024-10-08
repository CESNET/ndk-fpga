# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set FIFOX_BASE     "$OFM_PATH/comp/base/fifo/fifox"

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/dma_bus_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
    [list "FIFOX" $FIFOX_BASE "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/ptc_codapa_checker.vhd"
