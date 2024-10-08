// pkg.sv: Package for environment
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef PTC_PCIE_AXI2MFB_ENV_SV
`define PTC_PCIE_AXI2MFB_ENV_SV

package uvm_ptc_pcie_axi2mfb;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
