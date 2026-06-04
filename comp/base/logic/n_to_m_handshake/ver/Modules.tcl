# top.fdo:
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE      "$OFM_PATH/comp/base/pkg"

set COMPONENTS [list \
    [ list "VHDL_VER_TOOLS" "$OFM_PATH/comp/ver/vhdl_ver_tools/basics" "FULL"] \
    [ list "DUT"          "$ENTITY_BASE/.."             "FULL"] \
]

lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

lappend MOD "$ENTITY_BASE/testbench.vhd"
