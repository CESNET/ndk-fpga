/*
 * file: testbench.sv
 * brief: Testbench
 * author: Jan Kubalek <kubalek@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 * date: 2020
 */

import test_pkg::*;
import math_pkg::*;

module testbench;

    logic MI_CLK = 0;
    logic MI_RESET;
    logic CLK = 0;
    logic RESET;
    iMi32  MI(MI_CLK,MI_RESET);
    iMvbRx #(REGIONS,log2(PKT_MTU+1)+log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1) ETH_RX_MVB(CLK,RESET);
    iMfbRx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) ETH_RX_MFB(CLK,RESET);
    iMvbTx #(REGIONS,log2(PKT_MTU+1)+log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1) DMA_RX_MVB(CLK,RESET);
    iMfbTx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) DMA_RX_MFB(CLK,RESET);
    iMvbTx #(REGIONS,log2(PKT_MTU+1)+log2(TX_DMA_CHANNELS)+HDR_META_WIDTH) ETH_TX_MVB(CLK,RESET);
    iMfbTx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) ETH_TX_MFB(CLK,RESET);
    iMvbRx #(REGIONS,log2(PKT_MTU+1)+log2(TX_DMA_CHANNELS)+HDR_META_WIDTH) DMA_TX_MVB(CLK,RESET);
    iMfbRx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) DMA_TX_MFB(CLK,RESET);

    always #(CLK_PERIOD   /2) CLK    = ~CLK;
    always #(MI_CLK_PERIOD/2) MI_CLK = ~MI_CLK;

    DUT DUT_U (
        .CLK        (CLK       ),
        .RESET      (RESET     ),
        .MI_CLK     (MI_CLK    ),
        .MI_RESET   (MI_RESET  ),
        .MI         (MI        ),
        .ETH_RX_MVB (ETH_RX_MVB),
        .ETH_RX_MFB (ETH_RX_MFB),
        .DMA_RX_MVB (DMA_RX_MVB),
        .DMA_RX_MFB (DMA_RX_MFB),
        .ETH_TX_MVB (ETH_TX_MVB),
        .ETH_TX_MFB (ETH_TX_MFB),
        .DMA_TX_MVB (DMA_TX_MVB),
        .DMA_TX_MFB (DMA_TX_MFB)
    );

    TEST TEST_U (
        .CLK                (CLK       ),
        .RESET              (RESET     ),
        .MI_CLK             (MI_CLK    ),
        .MI_RESET           (MI_RESET  ),
        .MI                 (MI        ),
        .ETH_RX_MVB         (ETH_RX_MVB),
        .ETH_RX_MFB         (ETH_RX_MFB),
        .DMA_RX_MVB         (DMA_RX_MVB),
        .DMA_RX_MFB         (DMA_RX_MFB),
        .ETH_TX_MVB         (ETH_TX_MVB),
        .ETH_TX_MFB         (ETH_TX_MFB),
        .DMA_TX_MVB         (DMA_TX_MVB),
        .DMA_TX_MFB         (DMA_TX_MFB),

        .DMA_RX_MVB_MONITOR (DMA_RX_MVB),
        .DMA_RX_MFB_MONITOR (DMA_RX_MFB),
        .ETH_TX_MVB_MONITOR (ETH_TX_MVB),
        .ETH_TX_MFB_MONITOR (ETH_TX_MFB)
    );

endmodule
