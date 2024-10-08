# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE  "$OFM_PATH/comp/base/pkg"

lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

# Packages only for the simulation
lappend PACKAGES "$PKG_BASE/dma_bus_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/ver/vhdl_ver_tools/basics/basics_test_pkg.vhd"

lappend MOD "$ENTITY_BASE/dsp_counter_agilex_atom.vhd"
