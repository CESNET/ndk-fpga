# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set SV_UVM_BASE                     "$OFM_PATH/comp/uvm"

set COMPONENTS [list \
      [ list "SV_MFB_UVM_BASE"             "$SV_UVM_BASE/mfb"              "FULL"] \
      [ list "SV_LOGIC_VECTOR_UVM_BASE"    "$SV_UVM_BASE/logic_vector"     "FULL"] \
      [ list "SV_LV_ARRAY_MFB_UVM_BASE"    "$SV_UVM_BASE/logic_vector_array_mfb"  "FULL"] \
      [ list "SV_BYTE_ARRAY_MFB_UVM_BASE"  "$SV_UVM_BASE/byte_array_mfb"   "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/tbench/env/pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/tests/pkg.sv"

set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/testbench.sv"
