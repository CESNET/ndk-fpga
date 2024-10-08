// pkg.sv: Package for environment
// Copyright (C) 2022-2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef TX_DMA_CALYPTE_ENV_SV
`define TX_DMA_CALYPTE_ENV_SV

package uvm_tx_dma_calypte;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "sequence.sv"
    `include "sequencer.sv"
    `include "model.sv"
    `include "scoreboard.sv"
    `include "coverage.sv"
    `include "env.sv"

endpackage

`endif
