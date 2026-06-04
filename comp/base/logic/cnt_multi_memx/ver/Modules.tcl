# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jan Kubalek <kubalek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE "$OFM_PATH/comp/base/pkg"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
    [ list "VHDL_VER_TOOLS" "$OFM_PATH/comp/ver/vhdl_ver_tools/basics" "FULL"] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/testbench.vhd"
