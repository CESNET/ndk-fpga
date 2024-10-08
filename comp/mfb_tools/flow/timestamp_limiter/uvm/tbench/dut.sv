// dut.sv: Design under test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kříž <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


import test::*;

module DUT (
        input logic     CLK,
        input logic     RST,
        mfb_if.dut_rx   mfb_rx,
        mfb_if.dut_tx   mfb_tx,
        mi_if.dut_slave config_mi
    );

    localparam R_QUEUES = (QUEUES != 1) ? $clog2(QUEUES) : 1;

    logic [MFB_REGIONS*TIMESTAMP_WIDTH-1 : 0] timestamp;
    logic [MFB_REGIONS*MFB_META_WIDTH-1 : 0]  meta;
    logic [MFB_REGIONS*R_QUEUES-1 : 0]        mfb_queue;

    for (genvar regions = 0; regions < MFB_REGIONS; regions++) begin
        assign timestamp [(regions+1)*TIMESTAMP_WIDTH-1 -: TIMESTAMP_WIDTH] = mfb_rx.META[regions*RX_MFB_META_WIDTH + TIMESTAMP_WIDTH                            -1 -: TIMESTAMP_WIDTH];
        if (QUEUES !=1) begin
            assign mfb_queue [(regions+1)*$clog2(QUEUES)       -1 -: $clog2(QUEUES)       ] = mfb_rx.META[regions*RX_MFB_META_WIDTH + TIMESTAMP_WIDTH + $clog2(QUEUES)           -1 -: $clog2(QUEUES) ];
        end
        assign meta      [(regions+1)*MFB_META_WIDTH -1 -: MFB_META_WIDTH ] = mfb_rx.META[regions*RX_MFB_META_WIDTH + TIMESTAMP_WIDTH + $clog2(QUEUES) + MFB_META_WIDTH-1 -: MFB_META_WIDTH ];
    end

    MFB_TIMESTAMP_LIMITER #(
        .MFB_REGIONS       (MFB_REGIONS)      ,
        .MFB_REGION_SIZE   (MFB_REGION_SIZE)  ,
        .MFB_BLOCK_SIZE    (MFB_BLOCK_SIZE)   ,
        .MFB_ITEM_WIDTH    (MFB_ITEM_WIDTH)   ,
        .MFB_META_WIDTH    (MFB_META_WIDTH)   ,
        .MI_DATA_WIDTH     (MI_DATA_WIDTH)   ,
        .MI_ADDR_WIDTH     (MI_ADDR_WIDTH)   ,
        .CLK_FREQUENCY     (CLK_FREQUENCY)    ,
        .TIMESTAMP_WIDTH   (TIMESTAMP_WIDTH)  ,
        .TIMESTAMP_FORMAT  (TIMESTAMP_FORMAT) ,
        .BUFFER_SIZE       (BUFFER_SIZE)      ,
        .QUEUES            (QUEUES)           ,
        .PKT_MTU           (PKT_MTU)          ,
        .DEVICE            (DEVICE)
    ) VHDL_DUT_U (
        .CLK                (CLK)           ,
        .RESET              (RST)           ,

        .RX_MFB_DATA        (mfb_rx.DATA)   ,
        .RX_MFB_TIMESTAMP   (timestamp)     ,
        .RX_MFB_META        (meta)          ,
        .RX_MFB_QUEUE       (mfb_queue)     ,
        .RX_MFB_SOF_POS     (mfb_rx.SOF_POS),
        .RX_MFB_EOF_POS     (mfb_rx.EOF_POS),
        .RX_MFB_SOF         (mfb_rx.SOF)    ,
        .RX_MFB_EOF         (mfb_rx.EOF)    ,
        .RX_MFB_SRC_RDY     (mfb_rx.SRC_RDY),
        .RX_MFB_DST_RDY     (mfb_rx.DST_RDY),

        .TX_MFB_DATA        (mfb_tx.DATA)   ,
        .TX_MFB_META        (mfb_tx.META)   ,
        .TX_MFB_SOF_POS     (mfb_tx.SOF_POS),
        .TX_MFB_EOF_POS     (mfb_tx.EOF_POS),
        .TX_MFB_SOF         (mfb_tx.SOF)    ,
        .TX_MFB_EOF         (mfb_tx.EOF)    ,
        .TX_MFB_SRC_RDY     (mfb_tx.SRC_RDY),
        .TX_MFB_DST_RDY     (mfb_tx.DST_RDY),

        .MI_DWR             (config_mi.DWR),
        .MI_ADDR            (config_mi.ADDR),
        .MI_BE              (config_mi.BE),
        .MI_WR              (config_mi.WR),
        .MI_RD              (config_mi.RD),
        .MI_ARDY            (config_mi.ARDY),
        .MI_DRD             (config_mi.DRD),
        .MI_DRDY            (config_mi.DRDY)

    );


endmodule
