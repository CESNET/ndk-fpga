# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jan Kubalek <kubalek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE            "$OFM_PATH/comp/base/pkg"
set VER_BASE            "$OFM_PATH/comp/ver/vhdl_ver_tools/basics"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/dma_bus_pack.vhd"
set PACKAGES "$PACKAGES $VER_BASE/basics_test_pkg.vhd"

#set FIFOX_BASE       "$OFM_PATH/comp/base/fifo/fifox"

set COMPONENTS [list \
]
