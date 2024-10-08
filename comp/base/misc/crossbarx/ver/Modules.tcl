# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE "$OFM_PATH/comp/base/pkg"
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/dma_bus_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/ver/vhdl_ver_tools/basics/basics_test_pkg.vhd"

set COMPONENTS [list \
    [ list "UUT"               ".."                                     "FULL" ] \
    [ list "FIFOX_MULTI"       "$OFM_PATH/comp/base/fifo/fifox_multi"       "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/test_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/tester.vhd"
set MOD "$MOD $ENTITY_BASE/rx_buf.vhd"
set MOD "$MOD $ENTITY_BASE/tx_buf.vhd"
set MOD "$MOD $ENTITY_BASE/testbench.vhd"
