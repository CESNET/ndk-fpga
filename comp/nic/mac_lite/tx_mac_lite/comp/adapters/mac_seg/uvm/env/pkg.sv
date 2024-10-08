/*
 * file       : pkg.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: mag seq rx adapter
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef MAC_SEG_TX_VER
`define MAC_SEG_TX_VER

package uvm_mac_seg_tx

	`include "uvm_macros.svh";
	import uvm_pkg::*;

	`include "model.sv"
	`include "scoreboard.sv"
	`include "sequencer.sv"
	`include "env.sv"

	`include "sequence.sv"
endpackage

`endif

