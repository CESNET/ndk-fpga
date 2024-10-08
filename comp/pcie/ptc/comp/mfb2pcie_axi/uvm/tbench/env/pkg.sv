// pkg.sv: Package for environment
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef PTC_MFB2PCIE_AXI_ENV_SV
`define PTC_MFB2PCIE_AXI_ENV_SV

package uvm_ptc_mfb2pcie_axi;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
