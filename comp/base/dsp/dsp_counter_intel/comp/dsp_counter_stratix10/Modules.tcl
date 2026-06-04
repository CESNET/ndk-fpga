# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE  "$OFM_PATH/comp/base/pkg"

lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

# Component only for the simulation
lappend COMPONENTS [ list "VHDL_VER_TOOLS" "$OFM_PATH/comp/ver/vhdl_ver_tools/basics" "FULL"]

lappend MOD "$ENTITY_BASE/dsp_counter_stratix_10_atom.vhd"
