# top.fdo:
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE      "$OFM_PATH/comp/base/pkg"
set VER_PKG_BASE  "$OFM_PATH/comp/ver/vhdl_ver_tools/basics"

set COMPONENTS [list \
    [ list "DUT"          ".."             "FULL"] \
]

lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"
lappend PACKAGES "$PKG_BASE/dma_bus_pack.vhd"
lappend PACKAGES "$VER_PKG_BASE/basics_test_pkg.vhd"

lappend MOD "$ENTITY_BASE/testbench.vhd"
