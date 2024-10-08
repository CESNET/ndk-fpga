# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set MI_PIPE_BASE "$OFM_PATH/comp/mi_tools/pipe"

set PKG_BASE     "$OFM_PATH/comp/base/pkg"

set COMPONENTS [list \
[list "MI_PIPE" $MI_PIPE_BASE "FULL" ] \
]

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/dma_bus_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/ver/vhdl_ver_tools/basics/basics_test_pkg.vhd"

set PACKAGES "$PACKAGES $ENTITY_BASE/ab_init_pack.vhd"

set MOD "$MOD $ENTITY_BASE/mi_splitter_plus_gen.vhd"
set MOD "$MOD $ENTITY_BASE/ver/mi_splitter_plus_gen_wrapper.vhd"
