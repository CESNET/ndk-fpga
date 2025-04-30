/*
 * testbench.sv verification top module
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */


import test_pkg::*;

module testbench;

	logic    CLK = 0;
	logic    RESET;

    i_pcie_c #(DEVICE, PCIE_DATA_WIDTH) PCIE_C(CLK, RESET);
	iMi #(MI_WIDTH, MI_WIDTH) MI (CLK, RESET);


	always #(CLK_PERIOD/2) CLK = ~CLK;

	DUT
	DUT_U (
		.CLK           (CLK),
		.RESET         (RESET),
		.PCIE_C       (PCIE_C),
		.MI            (MI)
	);

	TEST TEST_U (
		.CLK           (CLK),
		.RESET         (RESET),
		.PCIE_C        (PCIE_C),
		.MI            (MI)
	);

    MI_PROPERTY #(
        .DIRECTION(1) //  0 => ASSERT(TX), 1 => ASSUME(RX)
    )
    MI_PROPERTY_U (
        .inf(MI)
    )

endmodule
