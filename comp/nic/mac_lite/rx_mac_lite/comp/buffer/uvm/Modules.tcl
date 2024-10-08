# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kříž <danielkriz@cesnet.cz>

# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set SV_UVM_BASE                     "$OFM_PATH/comp/uvm"

lappend COMPONENTS \
      [ list "SV_RESET"                     "$SV_UVM_BASE/reset"                    "FULL"] \
      [ list "SV_COMMON"                    "$SV_UVM_BASE/common"                   "FULL"] \
      [ list "SV_PROBE"                     "$SV_UVM_BASE/probe"                    "FULL"] \
      [ list "SV_BYTE_ARRAY_MFB_UVM_BASE"   "$SV_UVM_BASE/logic_vector_array_mfb"   "FULL"] \
      [ list "SV_LOGIC_VECTOR_MVB_UVM_BASE" "$SV_UVM_BASE/logic_vector_mvb"         "FULL"] \

lappend MOD "$ENTITY_BASE/tbench/env/pkg.sv"      \
            "$ENTITY_BASE/tbench/property.sv"     \
            "$ENTITY_BASE/tbench/dut.sv"          \
            "$ENTITY_BASE/tbench/pkg.sv"          \
            "$ENTITY_BASE/tbench/tests/pkg.sv"    \
            "$ENTITY_BASE/tbench/testbench.sv"    \
