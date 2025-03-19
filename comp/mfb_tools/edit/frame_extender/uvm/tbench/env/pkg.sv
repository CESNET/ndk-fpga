// pkg.sv: Package for the verification environment
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

`ifndef MFB_FRAME_EXTENDER_ENV_SV
`define MFB_FRAME_EXTENDER_ENV_SV

package uvm_mfb_frame_extender;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "model_data_item.sv"
    `include "model.sv"
    `include "meta_splitter.sv"
    `include "model_data_comparer.sv"
    `include "coverage_model.sv"
    `include "scoreboard.sv"
    `include "sequencer_length_extractor.sv"
    `include "virtual_sequencer.sv"
    `include "env.sv"

endpackage

`endif
