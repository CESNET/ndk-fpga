# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/dma_bus_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/ver/vhdl_ver_tools/basics/basics_test_pkg.vhd"

# Source files for implemented component
lappend MOD "$ENTITY_BASE/tsu_format_to_ns.vhd"

