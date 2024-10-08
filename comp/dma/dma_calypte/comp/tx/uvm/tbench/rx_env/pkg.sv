// pkg.sv: Package for the PCIE CQ environment
// Copyright (C) 2022-2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef TX_DMA_CALYPTE_CQ_ENV_PKG
`define TX_DMA_CALYPTE_CQ_ENV_PKG

package uvm_tx_dma_calypte_cq;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "sequence_item.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "driver.sv"
    `include "env.sv"
endpackage

`endif
