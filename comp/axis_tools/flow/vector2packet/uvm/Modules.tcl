# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [ list "SV_LV_AXI_BASE"      "$OFM_PATH/comp/uvm/logic_vector_array_axi"   "FULL"]
lappend COMPONENTS [ list "SV_RESET_BASE"       "$OFM_PATH/comp/uvm/reset"                    "FULL"]

lappend MOD "$ENTITY_BASE/tbench/env/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/test/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/generic.sv"
lappend MOD "$ENTITY_BASE/tbench/testbench.sv"
