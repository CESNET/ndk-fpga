//-- dut.sv: Design Under Test.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module DUT(
    input logic CLK,
    input logic RESET,
    iMvbRx.dut  RX_TRANS,
    iMvbTx.dut  RX_TRANS_MONITOR,
    iMvbRx.dut  RX_CONFS,
    iMvbTx.dut  RX_CONFS_MONITOR,
    iMvbTx.dut  TX_TRANS,
    iAFull.dut  FIFO_AFULL
);
    // -- DECLARATION OF LOGIC NEEDED FOR CONNECTION OF INTERFACES WITH DUT -----------------------------------------------------
    logic[ID_WIDTH-1:0]         mvb_rx_trans_id [MAX_RX_TRANS-1:0];
    logic[META_WIDTH-1:0]       mvb_rx_trans_meta [MAX_RX_TRANS-1:0];
    logic[MAX_RX_TRANS-1:0]     mvb_rx_trans_src_rdy ;
    logic                       mvb_rx_trans_dst_rdy;

    logic[ID_WIDTH-1:0]         mvb_rx_confs_id[MAX_ID_CONFS-1:0];
    logic[MAX_ID_CONFS-1:0]     mvb_rx_confs_vld;

    logic[ID_WIDTH-1:0]         mvb_tx_trans_id [MAX_TX_TRANS-1:0];
    logic[META_WIDTH-1:0]       mvb_tx_trans_meta [MAX_TX_TRANS-1:0];
    logic[MAX_TX_TRANS-1:0]     mvb_tx_trans_src_rdy;

    // -- ASSIGNING OF DATA FROM RX_TRANS INTERFACE TO RX_TRANS_MONITOR INTERFACE ------------------------------------------------
    assign RX_TRANS_MONITOR.DATA     = RX_TRANS.DATA;
    assign RX_TRANS_MONITOR.VLD      = RX_TRANS.VLD;
    assign RX_TRANS_MONITOR.SRC_RDY  = RX_TRANS.SRC_RDY;
    assign RX_TRANS_MONITOR.DST_RDY  = mvb_rx_trans_dst_rdy;

    // -- ASSIGNING OF DATA FROM RX_CONFS INTERFACE TO RX_CONFS_MONITOR INTERFACE ------------------------------------------------
    assign RX_CONFS_MONITOR.DATA      = RX_CONFS.DATA;
    assign RX_CONFS_MONITOR.VLD       = RX_CONFS.VLD;
    assign RX_CONFS_MONITOR.SRC_RDY   = RX_CONFS.SRC_RDY;
    assign RX_CONFS_MONITOR.DST_RDY   = RX_CONFS.DST_RDY;

    generate
        // -- ASSIGNING OF DATA FROM RX_TRANS INTERFACE TO LOGIC -----------------------------------------------------------------
        assign RX_TRANS.DST_RDY = mvb_rx_trans_dst_rdy;
        for (genvar i = 0 ; i < MAX_RX_TRANS ; i++ ) begin
            assign mvb_rx_trans_id[i]       = RX_TRANS.DATA[i*ITEM_WIDTH+ID_WIDTH-1:i*ITEM_WIDTH];
            assign mvb_rx_trans_meta[i]     = RX_TRANS.DATA[(i+1)*ITEM_WIDTH-1:i*ITEM_WIDTH+ID_WIDTH];
            assign mvb_rx_trans_src_rdy[i]  = RX_TRANS.SRC_RDY&&RX_TRANS.VLD[i];
        end
        // -- ASSIGNING OF DATA FROM RX_CONFS INTERFACE TO LOGIC -----------------------------------------------------------------
        assign RX_CONFS.DST_RDY=1;
        for (genvar i = 0 ; i < MAX_ID_CONFS; i++ ) begin
            assign mvb_rx_confs_id[i]  = RX_CONFS.DATA[(i+1)*ID_WIDTH-1:i*ID_WIDTH];
            assign mvb_rx_confs_vld[i] = RX_CONFS.SRC_RDY&&RX_CONFS.VLD[i];

        end
        // -- ASSIGNING OF DATA FROM LOGIC TO TX_TRANS INTERFACE -----------------------------------------------------------------
        for (genvar i = 0 ; i < MAX_TX_TRANS ; i++ ) begin
            assign TX_TRANS.DATA[i*ITEM_WIDTH+ID_WIDTH-1:i*ITEM_WIDTH]       = mvb_tx_trans_id[i];
            assign TX_TRANS.DATA[(i+1)*ITEM_WIDTH-1:i*ITEM_WIDTH+ID_WIDTH]   = mvb_tx_trans_meta[i];
            assign TX_TRANS.VLD[i]                                              = mvb_tx_trans_src_rdy[i];

        end
        assign TX_TRANS.SRC_RDY = |mvb_tx_trans_src_rdy;
    endgenerate

    // -- ASSIGNING DATA AND LOGIC TO DUT ----------------------------------------------------------------------------------------
    TRANS_SORTER #(
        .ID_WIDTH               (ID_WIDTH),
        .METADATA_WIDTH         (META_WIDTH),
        .RX_TRANSS              (MAX_RX_TRANS),
        .TX_TRANSS              (MAX_TX_TRANS),
        .ID_CONFS               (MAX_ID_CONFS),
        .MSIDT_BEHAV            (BEHAVIOUR),
        .MAX_SAME_ID_TRANS      (MAX_SAME_ID),
        .ALMOST_FULL_OFFSET     (ALMOST_FULL_OFFSET),
        .USE_SHAKEDOWN_FIFOX    (FIFOX_SHAKEDOWN_MODE)
    ) VHDL_TRANS_SORTER_U(
        .CLK                    (CLK),
        .RESET                  (RESET),
        .RX_TRANS_ID            (mvb_rx_trans_id),
        .RX_TRANS_META          (mvb_rx_trans_meta),
        .RX_TRANS_SRC_RDY       (mvb_rx_trans_src_rdy),
        .RX_TRANS_DST_RDY       (mvb_rx_trans_dst_rdy),
        .TRANS_FIFO_AFULL       (FIFO_AFULL.FIFO_AFULL),
        .TX_TRANS_ID            (mvb_tx_trans_id),
        .TX_TRANS_META          (mvb_tx_trans_meta),
        .TX_TRANS_SRC_RDY       (mvb_tx_trans_src_rdy),
        .TX_TRANS_DST_RDY       (TX_TRANS.DST_RDY),
        .RX_CONF_ID             (mvb_rx_confs_id),
        .RX_CONF_VLD            (mvb_rx_confs_vld)
    );
endmodule
