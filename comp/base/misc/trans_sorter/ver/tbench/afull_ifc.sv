//-- afull_ifc.sv: Interface for FIFO almost full signal.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// ----------------------------------------------------------------------------
// Interface for synchronization with CLK.
// and transmission FIFO_AFULL logic from DUT to scoreboard.
interface iAFull(input logic CLK);

    logic FIFO_AFULL;

    clocking cb @(posedge CLK);
        default input #1step output #500ps;
        input FIFO_AFULL;
    endclocking;

    modport dut(output FIFO_AFULL);

    modport tb(clocking cb);

endinterface
