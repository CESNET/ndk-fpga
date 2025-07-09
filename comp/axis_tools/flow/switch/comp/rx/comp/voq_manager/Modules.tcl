# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "AXIS_DEMUX" "$OFM_PATH/comp/axis_tools/logic/demux"  "FULL" ]
lappend COMPONENTS [ list "AXIS_FIFO"  "$OFM_PATH/comp/axis_tools/storage/fifo" "FULL" ]
lappend COMPONENTS [ list "AXIS_MUX"   "$OFM_PATH/comp/axis_tools/logic/mux"    "FULL" ]

lappend MOD "$ENTITY_BASE/voq_manager.vhd"
