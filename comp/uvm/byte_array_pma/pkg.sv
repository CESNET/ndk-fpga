/*
 * file       : pkg.sv
 * description: rx environment pkg
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * Copyright (C) 2021 CESNET z. s. p. o.
*/

`ifndef BYTE_ARRAY_PMA_ENV_PKG
`define BYTE_ARRAY_PMA_ENV_PKG

package uvm_byte_array_pma;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "data_reg.sv"
    `include "sequencer.sv"
    `include "sequence.sv"
    `include "sequence_seq_err_inj.sv"
    `include "sequence_hdr_err_inj.sv"
    `include "sequence_lib.sv"
    `include "monitor.sv"
    `include "env.sv"

endpackage

`endif
