/*
 * test_pkg.sv file with verification parameters
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

package test_pkg;

	/* Clocks and reset */
    parameter SIMULATION_DURATION = 40ms;

    parameter CLK_PERIOD = 10ns;
	parameter RESET_TIME = 30*CLK_PERIOD;

    parameter DEVICE          = "STRATIX10"; // "STRATIX10"; //"ULTRASCALE";
    parameter PCIE_DATA_WIDTH = 512;

    parameter MRRS = 512;

    parameter VERBOSE = 0;
    parameter MI_WIDTH = 32;
endpackage
