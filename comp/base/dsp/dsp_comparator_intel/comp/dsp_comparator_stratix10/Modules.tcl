# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

# Packages only for the simulation
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/dma_bus_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/ver/vhdl_ver_tools/basics/basics_test_pkg.vhd"

set MOD "$MOD $ENTITY_BASE/dsp_comparator_stratix_10_atom.vhd"
