# Modules.tcl: Components include script
# Copyright (C) 2017 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

# Source files for implemented component

# Set VHDL standard to "VHDL" (98) instead of default "VHDL 2008" for this file
lappend MOD [list "$ENTITY_BASE/dp_bram_behav.vhd" VIVADO_SET_PROPERTY [list -quiet FILE_TYPE {VHDL}]]
