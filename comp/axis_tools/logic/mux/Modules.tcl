# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "GEN_MUX"   "$OFM_PATH/comp/base/logic/mux"   "FULL" ]
lappend COMPONENTS [ list "GEN_DEMUX" "$OFM_PATH/comp/base/logic/demux" "FULL" ]

lappend MOD "$ENTITY_BASE/mux.vhd"
