# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Tomas Hak <xhakto01@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths
set DEC1FN_BASE      "$OFM_PATH/comp/base/logic/dec1fn"
set GEN_MUX_BASE     "$OFM_PATH/comp/base/logic/mux"
set GEN_DEMUX_BASE   "$OFM_PATH/comp/base/logic/demux"
set SPEED_METER_BASE "$OFM_PATH/comp/mfb_tools/logic/speed_meter"
set FIRST_ONE_BASE   "$OFM_PATH/comp/base/logic/first_one"

# Files
lappend COMPONENTS [ list "DEC1FN_ENABLE" $DEC1FN_BASE      "FULL" ]
lappend COMPONENTS [ list "GEN_MUX"       $GEN_MUX_BASE     "FULL" ]
lappend COMPONENTS [ list "GEN_DEMUX"     $GEN_DEMUX_BASE   "FULL" ]
lappend COMPONENTS [ list "SPEED_METER"   $SPEED_METER_BASE "FULL" ]
lappend COMPONENTS [ list "FIRST_ONE"     $FIRST_ONE_BASE   "FULL" ]

lappend MOD "$ENTITY_BASE/rate_limiter.vhd"

lappend MOD "$ENTITY_BASE/DevTree.tcl"
