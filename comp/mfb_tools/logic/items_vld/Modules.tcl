# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z.s.p.o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


# Set paths
set PKG_BASE       "$OFM_PATH/comp/base/pkg"
set LOGIC_BASE     "$OFM_PATH/comp/base/logic/"
set MFB_LOGIC_BASE "$OFM_PATH/comp/mfb_tools/logic/"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

lappend COMPONENTS [ list "BIN2HOT"         "$LOGIC_BASE/bin2hot"             "FULL" ]
lappend COMPONENTS [ list "ONES_INSERTOR"   "$LOGIC_BASE/ones_insertor"       "FULL" ]
lappend COMPONENTS [ list "OFFSET_REACHED"  "$MFB_LOGIC_BASE/offset_reached"  "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/validation_prepare_r.vhd"
lappend MOD "$ENTITY_BASE/validation_prepare.vhd"
lappend MOD "$ENTITY_BASE/validation_do.vhd"
lappend MOD "$ENTITY_BASE/mfb_items_vld.vhd"
