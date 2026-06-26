//-- tbench.sv: Testbench
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author: Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench #(
    int unsigned    INPUT_WIDTH,
    int unsigned    BOX_WIDTH,
    int unsigned    BOX_CNT,
    logic           READ_PRIOR,
    logic           CLEAR_BY_READ,
    logic           CLEAR_BY_RST,
    string          DEVICE
);

    localparam int unsigned REQ_WIDTH  = 1 + INPUT_WIDTH + $clog2(BOX_CNT);
    localparam int unsigned RESP_WIDTH = BOX_WIDTH;

    localparam int unsigned ADDR_WIDTH = $clog2(BOX_CNT);

    typedef uvm_component_registry#(test::ex_test #(
        INPUT_WIDTH,
        BOX_WIDTH,
        BOX_CNT,
        READ_PRIOR,
        CLEAR_BY_READ,
        CLEAR_BY_RST,
        DEVICE,
        REQ_WIDTH,
        RESP_WIDTH,
        ADDR_WIDTH
    ), "test::ex_test") type_id;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK = 0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if reset(CLK);

    mvb_if #(1, REQ_WIDTH)  mvb_req  (CLK);
    mvb_if #(1, RESP_WIDTH) mvb_resp (CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD) CLK = ~CLK;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;
        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);

        uvm_config_db#(virtual mvb_if #(1, REQ_WIDTH)) ::set(null, "", "vif_req",  mvb_req);
        uvm_config_db#(virtual mvb_if #(1, RESP_WIDTH))::set(null, "", "vif_resp", mvb_resp);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME", UVM_NO_ACTION);

        // Stop reporting for us unusefull information
        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $write("Verification finished successfully!\n");
        $stop(2);
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // dut
    dut #(
        .INPUT_WIDTH  (INPUT_WIDTH),
        .BOX_WIDTH    (BOX_WIDTH),
        .BOX_CNT      (BOX_CNT),
        .READ_PRIOR   (READ_PRIOR),
        .CLEAR_BY_READ(CLEAR_BY_READ),
        .CLEAR_BY_RST (CLEAR_BY_RST),
        .DEVICE       (DEVICE),
        .REQ_WIDTH    (REQ_WIDTH),
        .RESP_WIDTH   (RESP_WIDTH)
    ) DUT_U (
        .CLK        (CLK),
        .RST        (reset.RESET),
        .mvb_req    (mvb_req),
        .mvb_resp   (mvb_resp)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties

    mvb_property  #(
        .ITEMS       (1),
        .ITEM_WIDTH  (REQ_WIDTH)
    )
    property_wr (
        .RESET  (reset.RESET),
        .vif    (mvb_req)
    );

    mvb_property #(
        .ITEMS       (1),
        .ITEM_WIDTH  (RESP_WIDTH)
    )
    property_rd(
        .RESET  (reset.RESET),
        .vif    (mvb_resp)
    );

endmodule
