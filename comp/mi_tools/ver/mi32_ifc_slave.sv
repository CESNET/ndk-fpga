/*!
 * \file       mi32_ifc_slave.sv
 * \brief      MI32 interface - slave version
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
 */

interface iMi32 (input logic CLK, RESET);
	logic [31:0] ADDR;
	logic [31:0] DWR;
	logic [31:0] DRD;
	logic [3:0] BE;
	logic RD;
	logic WR;
	logic ARDY;
	logic DRDY;

	clocking monitor_cb @(posedge CLK);
		input ADDR, DWR, DRD, BE, RD, WR, ARDY, DRDY;
	endclocking

	modport responder (
			input CLK,
			output ARDY, DRDY, DRD,
			input ADDR, DWR, BE, RD, WR);

	modport dut (
			output ADDR,
			output DWR,
			output BE,
			output RD,
			output WR,
			input  ARDY,
			input  DRDY,
			input  DRD
	);

	// --------------------------------------------------------------------------
	// -- Interface properties/assertions
	// --------------------------------------------------------------------------

	// -- While RESET RD inactive ----------------------------------------
	// RD may be active only if RESET is inactive.
	property RESETR;
		@(posedge CLK) (RESET)|->(not RD);
	endproperty

	assert property (RESETR)
		else $error("RD is active during reset.");

	// -- While RESET WR inactive ----------------------------------------
	// WR may be active only if RESET is inactive.
	property RESETW;
		@(posedge CLK) (RESET)|->(not WR);
	endproperty

	assert property (RESETW)
		else $error("WR is active during reset.");

	// -- WR never together with RD ---------------------------------------
	// WR can not be active together with RD.
	property RDnottogetherWR;
		@(posedge CLK) (RD)|->(!WR);
	endproperty

	assert property (RDnottogetherWR)
		else $error("RD and WR signals can not be active at the same cycle.");

endinterface
