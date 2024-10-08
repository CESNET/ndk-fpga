# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET
# Author(s): Jan Kubalek <xkubal11@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set PKG_BASE      "$OFM_PATH/comp/base/pkg"
set VER_PKG_BASE  "$OFM_PATH/comp/ver/vhdl_ver_tools/basics"

set COMPONENTS [list \
    [ list "DUT"          ".."             "FULL"] \
]

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/dma_bus_pack.vhd"
set PACKAGES "$PACKAGES $VER_PKG_BASE/basics_test_pkg.vhd"

set MOD "$MOD $ENTITY_BASE/test_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/testbench.vhd"
