/*
 * file       : pkg.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: byte_array to mii enviroment pkg
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef BYTE_ARRAY_LII_ENV_PKG
`define BYTE_ARRAY_LII_ENV_PKG

package uvm_byte_array_lii;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "sequencer.sv"
    `include "sequence_simple.sv"
    `include "sequence_simple_rx_random_link_status.sv"
    `include "sequence_simple_rx_random_errors.sv"
    `include "sequence_simple_rx_error_with_random_link_status.sv"
    `include "sequence_simple_rx_random_sof.sv"
    `include "sequence_simple_rx_sof_after_eof.sv"
    `include "sequence_simple_tx_mac.sv"
    `include "sequence_not_rdy_once_for_32_ticks_tx.sv"
    `include "sequence_simple_tx_random_rdy.sv"
    `include "sequence_simple_eth_phy.sv"
    `include "sequence_simple_eth_phy_no_gaps.sv"
    `include "sequence_simple_eth_phy_const_gaps.sv"
    `include "sequence_simple_eth_phy_err_crc.sv"
    `include "sequence_lib.sv"
    `include "monitor.sv"
    `include "env.sv"

endpackage

`endif
