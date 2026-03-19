# Modules.tcl: Components include script
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "BARREL_SHIFTER_GEN" "$OFM_PATH/comp/base/logic/barrel_shifter" "FULL" ]

lappend MOD "$ENTITY_BASE/axis_head_trimmer.vhd"
