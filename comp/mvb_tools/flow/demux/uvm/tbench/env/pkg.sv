// pkg.sv: Package for environment
// Copyright (C) 2023-2024 CESNET z. s. p. o.
// Author: Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
//         Vladislav Valek <valekv@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

`ifndef GEM_MVB_DEMUX_ENV_SV
`define GEN_MVB_DEMUX_ENV_SV

package uvm_mvb_demux;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage

`endif
