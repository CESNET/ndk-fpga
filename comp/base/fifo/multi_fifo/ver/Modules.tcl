# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set PKG_BASE                 "$OFM_PATH/comp/base/pkg"
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/dma_bus_pack.vhd"

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/ver/vhdl_ver_tools/basics/basics_test_pkg.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
   [ list "DUT"			".." 			  "FULL"      ] \
]]
