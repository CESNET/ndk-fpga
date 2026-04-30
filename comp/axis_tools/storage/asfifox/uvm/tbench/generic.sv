//-- generic.sv: Generic package
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


package uvm_generic;

    parameter int unsigned ITEMS               = 64;
    parameter int unsigned ITEM_WIDTH          = 8;

    parameter int unsigned TUSER_WIDTH         = 2;
    parameter int unsigned FIFO_ITEMS          = 512;
    parameter string RAM_TYPE                  = "BRAM";
    parameter bit FWFT_MODE                    = 1;
    parameter bit OUTPUT_REG                   = 1;
    parameter int unsigned AFULL_OFFSET        = FIFO_ITEMS/2;
    parameter int unsigned AEMPTY_OFFSET       = FIFO_ITEMS/2;
    parameter string DEVICE                    = "AGILEX";

    parameter time CLK_RX_PERIOD = 4ns;
    parameter time CLK_TX_PERIOD = 8ns;

endpackage
