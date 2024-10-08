# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set MFB_PIPE_BASE "$OFM_PATH/comp/mfb_tools/flow/pipe"

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set COMPONENTS [concat $COMPONENTS [list \
    [ list "MFB_PIPE" $MFB_PIPE_BASE "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/pcie_axicc2mfb.vhd"
