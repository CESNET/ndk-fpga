// pkg.sv: pcie top package verification
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:   Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef PCIE_ENV_TOP_SV
`define PCIE_ENV_TOP_SV

package uvm_pcie_top;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "sequence_mi.sv"
    `include "sequence_dma_rq.sv"
    `include "sequence.sv"
    `include "model_ptc.sv"
    `include "model_mtc.sv"
    `include "model_base.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
