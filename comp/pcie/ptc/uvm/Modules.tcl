# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set SV_UVM_BASE                     "$OFM_PATH/comp/uvm"

set COMPONENTS [list \
      [ list "UVM_BASE"                           "$OFM_PATH/comp/ver"                    "FULL"] \
      [ list "SV_RESET"                           "$SV_UVM_BASE/reset"                    "FULL"] \
      [ list "SV_MFB_UVM_BASE"                    "$SV_UVM_BASE/mfb"                      "FULL"] \
      [ list "SV_MVB_UVM_BASE"                    "$SV_UVM_BASE/mvb"                      "FULL"] \
      [ list "SV_LOGIC_VECTOR_UVM_BASE"           "$SV_UVM_BASE/logic_vector"             "FULL"] \
      [ list "SV_BYTE_ARRAY_MFB_UVM_BASE"         "$SV_UVM_BASE/logic_vector_array_mfb"   "FULL"] \
      [ list "SV_LOGIC_VECTOR_MVB_UVM_BASE"       "$SV_UVM_BASE/logic_vector_mvb"         "FULL"] \
      [ list "SV_LOGIC_VECTOR_ARRAY_AXI_UVM_BASE" "$SV_UVM_BASE/logic_vector_array_axi"   "FULL"] \
]

set MOD "$MOD $OFM_PATH/comp/base/pkg/dma_bus_pack.sv"

set MOD "$MOD $ENTITY_BASE/tbench/info/pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dma_up_env/pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/info_rc/pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/pcie_rc/pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/env/pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/tests/pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/property.sv"

set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/testbench.sv"
