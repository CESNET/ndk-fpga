# dp_bmem.tcl: Local constrains for DP_BMEM
# Copyright (C) 2014 CESNET
# Author: Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# $Id$
#

set ram_mode [get_property RAM_MODE [lindex [get_cells *memory_reg*] 0]]

if { $ram_mode == "SDP" } {
   set_false_path -to [get_pins *memory_reg*/REGCEB]
   set_false_path -to [get_pins *memory_reg*/RSTREGB]
}
