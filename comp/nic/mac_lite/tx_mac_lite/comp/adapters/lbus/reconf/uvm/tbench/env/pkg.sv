// pkg.sv: Package for environment
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Vladislav Valek <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef MFB_TO_LBUS_ADAPTER_ENV_SV
`define MFB_TO_LBUS_ADAPTER_ENV_SV

package uvm_mfb_to_lbus_adapter;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
