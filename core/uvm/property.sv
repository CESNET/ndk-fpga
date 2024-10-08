//-- property.sv: bus property of aplication core
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause



module app_core_property #(ETH_STREAMS, DMA_STREAMS, REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, CHECK_RX)
    (
        input RESET,
        mfb_if eth_tx_mfb[ETH_STREAMS],
        //mvb_if eth_tx_mvb[ETH_STREAMS],
        mfb_if dma_tx_mfb[DMA_STREAMS],
        mvb_if dma_tx_mvb[DMA_STREAMS],

        mfb_if eth_rx_mfb[ETH_STREAMS],
        mvb_if eth_rx_mvb[ETH_STREAMS],
        mfb_if dma_rx_mfb[DMA_STREAMS],
        mvb_if dma_rx_mvb[DMA_STREAMS]
    );


    localparam DMA_RX_MVB_WIDTH = $clog2(test_pkg::DMA_PKT_MTU+1)+test_pkg::DMA_HDR_META_WIDTH+$clog2(test_pkg::DMA_TX_CHANNELS);
    localparam DMA_TX_MVB_WIDTH = $clog2(test_pkg::DMA_PKT_MTU+1)+test_pkg::DMA_HDR_META_WIDTH+$clog2(test_pkg::DMA_RX_CHANNELS) + 1;

    ////////////////////////////////////////
    // ETH INTERFACE
    for (genvar eth_it = 0; eth_it < ETH_STREAMS; eth_it++) begin : eth
        mfb_property #(
            .REGIONS      (REGIONS),
            .REGION_SIZE  (MFB_REGION_SIZE),
            .BLOCK_SIZE   (MFB_BLOCK_SIZE),
            .ITEM_WIDTH   (MFB_ITEM_WIDTH),
            .META_WIDTH   (test_pkg::ETH_TX_HDR_WIDTH)
        )
        mfb_tx_bus (
            .RESET (RESET),
            .vif   (eth_tx_mfb[eth_it])
        );

        //mvb_property #(
        //)
        //mvb_tx_bus (
        //    .RESET (RESET),
        //    .vif   (eth_tx_mvb[eth_it])
        //);
        if (CHECK_RX == 1'b1) begin
            mfb_property #(
                .REGIONS      (REGIONS),
                .REGION_SIZE  (MFB_REGION_SIZE),
                .BLOCK_SIZE   (MFB_BLOCK_SIZE),
                .ITEM_WIDTH   (MFB_ITEM_WIDTH),
                .META_WIDTH   (0)
            )
            mfb_rx_bus (
                .RESET (RESET),
                .vif   (eth_rx_mfb[eth_it])
            );

            mvb_property #(
                .ITEMS      (REGIONS),
                .ITEM_WIDTH (test_pkg::ETH_RX_HDR_WIDTH)
            )
            mvb_rx_bus (
                .RESET (RESET),
                .vif   (eth_rx_mvb[eth_it])
            );
        end
    end

    ////////////////////////////////////////
    // DMA INTERFACE
    for (genvar dma_it = 0; dma_it < DMA_STREAMS; dma_it++) begin : dma
        mfb_property #(
            .REGIONS      (REGIONS),
            .REGION_SIZE  (MFB_REGION_SIZE),
            .BLOCK_SIZE   (MFB_BLOCK_SIZE),
            .ITEM_WIDTH   (MFB_ITEM_WIDTH),
            .META_WIDTH   (0)
        )
        mfb_tx_bus (
            .RESET (RESET),
            .vif   (dma_tx_mfb[dma_it])
        );

        mvb_property #(
                .ITEMS      (REGIONS),
                .ITEM_WIDTH (DMA_TX_MVB_WIDTH)
        )
        mvb_tx_bus (
            .RESET (RESET),
            .vif   (dma_tx_mvb[dma_it])
        );


        if (CHECK_RX == 1'b1) begin
            mfb_property #(
                .REGIONS      (REGIONS),
                .REGION_SIZE  (MFB_REGION_SIZE),
                .BLOCK_SIZE   (MFB_BLOCK_SIZE),
                .ITEM_WIDTH   (MFB_ITEM_WIDTH),
                .META_WIDTH   (0)
            )
            mfb_rx_bus (
                .RESET (RESET),
                .vif   (dma_rx_mfb[dma_it])
            );

            mvb_property #(
                .ITEMS      (REGIONS),
                .ITEM_WIDTH (DMA_RX_MVB_WIDTH)
            )
            mvb_rx_bus (
                .RESET (RESET),
                .vif   (dma_rx_mvb[dma_it])
            );
        end
    end
endmodule
