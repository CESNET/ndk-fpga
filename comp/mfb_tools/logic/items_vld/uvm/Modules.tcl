# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set SV_UVM_BASE                     "$OFM_PATH/comp/uvm"

lappend COMPONENTS \
      [ list "SV_RESET"                            "$SV_UVM_BASE/reset"                    "FULL"] \
      [ list "PCAP"                                "$SV_UVM_BASE/pcap"                     "FULL"] \
      [ list "SV_MFB_UVM_BASE"                     "$SV_UVM_BASE/mfb"                      "FULL"] \
      [ list "SV_MVB_UVM_BASE"                     "$SV_UVM_BASE/mvb"                      "FULL"] \
      [ list "SV_LOGIC_VECTOR_ARRAY_MFB_UVM_BASE"  "$SV_UVM_BASE/logic_vector_array_mfb"   "FULL"] \
      [ list "SV_LOGIC_VECTOR_MVB_UVM_BASE"        "$SV_UVM_BASE/logic_vector_mvb"        "FULL"]  \

lappend MOD "$ENTITY_BASE/tbench/info/pkg.sv"  \
            "$ENTITY_BASE/tbench/env/pkg.sv"   \
            "$ENTITY_BASE/tbench/tests/pkg.sv" \
            "$ENTITY_BASE/tbench/property.sv"  \
            "$ENTITY_BASE/tbench/dut.sv"       \
            "$ENTITY_BASE/tbench/testbench.sv" \
