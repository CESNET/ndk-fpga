# mux.vhd: General width MVB MUX
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MUX_BASE        "$OFM_PATH/comp/base/logic/mux"
set DEMUX_BASE      "$OFM_PATH/comp/base/logic/demux"
set MVB_FIFO_BASE   "$OFM_PATH/comp/mvb_tools/storage/fifox"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "MUX"         $MUX_BASE       "FULL" ]
lappend COMPONENTS [ list "DEMUX"       $DEMUX_BASE     "FULL" ]
lappend COMPONENTS [ list "MVB_FIFO"    $MVB_FIFO_BASE  "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/mux.vhd"
lappend MOD "$ENTITY_BASE/mux2.vhd"
