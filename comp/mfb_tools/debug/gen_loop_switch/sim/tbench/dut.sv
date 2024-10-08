/*
 * file: dut.sv
 * brief: Design Under Test
 * author: Jan Kubalek <kubalek@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 * date: 2020
 */

import test_pkg::*;
import math_pkg::*;

module DUT (
    input logic MI_CLK,
    input logic MI_RESET,
    input logic CLK,
    input logic RESET,
    iMi32.dut  MI,
    iMvbRx.dut ETH_RX_MVB,
    iMfbRx.dut ETH_RX_MFB,
    iMfbTx.dut DMA_RX_MFB,
    iMvbTx.dut DMA_RX_MVB,
    iMvbTx.dut ETH_TX_MVB,
    iMfbTx.dut ETH_TX_MFB,
    iMvbRx.dut DMA_TX_MVB,
    iMfbRx.dut DMA_TX_MFB
);

    logic [ETH_RX_MVB.ITEM_WIDTH-1:0] arr_ETH_RX_MVB_DATA    [REGIONS-1:0];
    logic [log2(PKT_MTU+1)      -1:0] arr_ETH_RX_MVB_LEN     [REGIONS-1:0];
    logic [log2(RX_DMA_CHANNELS)-1:0] arr_ETH_RX_MVB_CHANNEL [REGIONS-1:0];
    logic [HDR_META_WIDTH    -1:0] arr_ETH_RX_MVB_HDR_META[REGIONS-1:0];
    logic [1                    -1:0] arr_ETH_RX_MVB_DISCARD [REGIONS-1:0];

    logic [ETH_TX_MVB.ITEM_WIDTH-1:0] arr_ETH_TX_MVB_DATA    [REGIONS-1:0];
    logic [log2(PKT_MTU+1)      -1:0] arr_ETH_TX_MVB_LEN     [REGIONS-1:0];
    logic [log2(TX_DMA_CHANNELS)-1:0] arr_ETH_TX_MVB_CHANNEL [REGIONS-1:0];
    logic [HDR_META_WIDTH    -1:0] arr_ETH_TX_MVB_HDR_META[REGIONS-1:0];

    logic [DMA_RX_MVB.ITEM_WIDTH-1:0] arr_DMA_RX_MVB_DATA    [REGIONS-1:0];
    logic [log2(PKT_MTU+1)      -1:0] arr_DMA_RX_MVB_LEN     [REGIONS-1:0];
    logic [log2(RX_DMA_CHANNELS)-1:0] arr_DMA_RX_MVB_CHANNEL [REGIONS-1:0];
    logic [HDR_META_WIDTH    -1:0] arr_DMA_RX_MVB_HDR_META[REGIONS-1:0];
    logic [1                    -1:0] arr_DMA_RX_MVB_DISCARD [REGIONS-1:0];

    logic [DMA_TX_MVB.ITEM_WIDTH-1:0] arr_DMA_TX_MVB_DATA    [REGIONS-1:0];
    logic [log2(PKT_MTU+1)      -1:0] arr_DMA_TX_MVB_LEN     [REGIONS-1:0];
    logic [log2(TX_DMA_CHANNELS)-1:0] arr_DMA_TX_MVB_CHANNEL [REGIONS-1:0];
    logic [HDR_META_WIDTH    -1:0] arr_DMA_TX_MVB_HDR_META[REGIONS-1:0];

    logic ETH_RX_MVB_DATA    [REGIONS*ETH_RX_MVB.ITEM_WIDTH-1:0];
    logic ETH_RX_MVB_LEN     [REGIONS*log2(PKT_MTU+1)-1:0];
    logic ETH_RX_MVB_CHANNEL [REGIONS*log2(RX_DMA_CHANNELS)-1:0];
    logic ETH_RX_MVB_HDR_META[REGIONS*HDR_META_WIDTH-1:0];
    logic ETH_RX_MVB_DISCARD [REGIONS*1-1:0];

    logic ETH_TX_MVB_DATA    [REGIONS*ETH_TX_MVB.ITEM_WIDTH-1:0];
    logic ETH_TX_MVB_LEN     [REGIONS*log2(PKT_MTU+1)-1:0];
    logic ETH_TX_MVB_CHANNEL [REGIONS*log2(TX_DMA_CHANNELS)-1:0];
    logic ETH_TX_MVB_HDR_META[REGIONS*HDR_META_WIDTH-1:0];

    logic DMA_RX_MVB_DATA    [REGIONS*DMA_RX_MVB.ITEM_WIDTH-1:0];
    logic DMA_RX_MVB_LEN     [REGIONS*log2(PKT_MTU+1)-1:0];
    logic DMA_RX_MVB_CHANNEL [REGIONS*log2(RX_DMA_CHANNELS)-1:0];
    logic DMA_RX_MVB_HDR_META[REGIONS*HDR_META_WIDTH-1:0];
    logic DMA_RX_MVB_DISCARD [REGIONS*1-1:0];

    logic DMA_TX_MVB_DATA    [REGIONS*DMA_TX_MVB.ITEM_WIDTH-1:0];
    logic DMA_TX_MVB_LEN     [REGIONS*log2(PKT_MTU+1)-1:0];
    logic DMA_TX_MVB_CHANNEL [REGIONS*log2(TX_DMA_CHANNELS)-1:0];
    logic DMA_TX_MVB_HDR_META[REGIONS*HDR_META_WIDTH-1:0];

    GEN_LOOP_SWITCH #(
        .REGIONS            (REGIONS          ),
        .REGION_SIZE        (REGION_SIZE      ),
        .BLOCK_SIZE         (BLOCK_SIZE       ),
        .ITEM_WIDTH         (ITEM_WIDTH       ),
        .PKT_MTU            (PKT_MTU          ),
        .RX_DMA_CHANNELS    (RX_DMA_CHANNELS  ),
        .TX_DMA_CHANNELS    (TX_DMA_CHANNELS  ),
        .NPP_HDR_SIZE       (NPP_HDR_SIZE     ),
        .HDR_META_WIDTH     (HDR_META_WIDTH   ),
        .RX_HDR_INS_EN      (RX_HDR_INS_EN    ),
        .SAME_CLK           (SAME_CLK         ),
        .MI_PIPE_EN         (MI_PIPE_EN       ),
        .DEVICE             (DEVICE           )
    ) VHDL_DUT_U (
        .MI_CLK              (MI_CLK  ),
        .MI_RESET            (MI_RESET),

        .MI_DWR              (MI.DWR ),
        .MI_ADDR             (MI.ADDR),
        .MI_BE               (MI.BE  ),
        .MI_RD               (MI.RD  ),
        .MI_WR               (MI.WR  ),
        .MI_ARDY             (MI.ARDY),
        .MI_DRD              (MI.DRD ),
        .MI_DRDY             (MI.DRDY),

        .CLK                 (CLK  ),
        .RESET               (RESET),

        .ETH_RX_MVB_LEN      (ETH_RX_MVB_LEN     ),
        .ETH_RX_MVB_CHANNEL  (ETH_RX_MVB_CHANNEL ),
        .ETH_RX_MVB_HDR_META (ETH_RX_MVB_HDR_META),
        .ETH_RX_MVB_DISCARD  (ETH_RX_MVB_DISCARD ),
        .ETH_RX_MVB_VLD      (ETH_RX_MVB.VLD     ),
        .ETH_RX_MVB_SRC_RDY  (ETH_RX_MVB.SRC_RDY ),
        .ETH_RX_MVB_DST_RDY  (ETH_RX_MVB.DST_RDY ),

        .ETH_RX_MFB_DATA     (ETH_RX_MFB.DATA    ),
        .ETH_RX_MFB_SOF      (ETH_RX_MFB.SOF     ),
        .ETH_RX_MFB_EOF      (ETH_RX_MFB.EOF     ),
        .ETH_RX_MFB_SOF_POS  (ETH_RX_MFB.SOF_POS ),
        .ETH_RX_MFB_EOF_POS  (ETH_RX_MFB.EOF_POS ),
        .ETH_RX_MFB_SRC_RDY  (ETH_RX_MFB.SRC_RDY ),
        .ETH_RX_MFB_DST_RDY  (ETH_RX_MFB.DST_RDY ),

        .ETH_TX_MVB_LEN      (ETH_TX_MVB_LEN     ),
        .ETH_TX_MVB_CHANNEL  (ETH_TX_MVB_CHANNEL ),
        .ETH_TX_MVB_HDR_META (ETH_TX_MVB_HDR_META),
        .ETH_TX_MVB_VLD      (ETH_TX_MVB.VLD     ),
        .ETH_TX_MVB_SRC_RDY  (ETH_TX_MVB.SRC_RDY ),
        .ETH_TX_MVB_DST_RDY  (ETH_TX_MVB.DST_RDY ),

        .ETH_TX_MFB_DATA     (ETH_TX_MFB.DATA    ),
        .ETH_TX_MFB_SOF      (ETH_TX_MFB.SOF     ),
        .ETH_TX_MFB_EOF      (ETH_TX_MFB.EOF     ),
        .ETH_TX_MFB_SOF_POS  (ETH_TX_MFB.SOF_POS ),
        .ETH_TX_MFB_EOF_POS  (ETH_TX_MFB.EOF_POS ),
        .ETH_TX_MFB_SRC_RDY  (ETH_TX_MFB.SRC_RDY ),
        .ETH_TX_MFB_DST_RDY  (ETH_TX_MFB.DST_RDY ),

        .DMA_RX_MVB_LEN      (DMA_RX_MVB_LEN     ),
        .DMA_RX_MVB_CHANNEL  (DMA_RX_MVB_CHANNEL ),
        .DMA_RX_MVB_HDR_META (DMA_RX_MVB_HDR_META),
        .DMA_RX_MVB_DISCARD  (DMA_RX_MVB_DISCARD ),
        .DMA_RX_MVB_VLD      (DMA_RX_MVB.VLD     ),
        .DMA_RX_MVB_SRC_RDY  (DMA_RX_MVB.SRC_RDY ),
        .DMA_RX_MVB_DST_RDY  (DMA_RX_MVB.DST_RDY ),

        .DMA_RX_MFB_DATA     (DMA_RX_MFB.DATA    ),
        .DMA_RX_MFB_SOF      (DMA_RX_MFB.SOF     ),
        .DMA_RX_MFB_EOF      (DMA_RX_MFB.EOF     ),
        .DMA_RX_MFB_SOF_POS  (DMA_RX_MFB.SOF_POS ),
        .DMA_RX_MFB_EOF_POS  (DMA_RX_MFB.EOF_POS ),
        .DMA_RX_MFB_SRC_RDY  (DMA_RX_MFB.SRC_RDY ),
        .DMA_RX_MFB_DST_RDY  (DMA_RX_MFB.DST_RDY ),

        .DMA_TX_MVB_LEN      (DMA_TX_MVB_LEN     ),
        .DMA_TX_MVB_CHANNEL  (DMA_TX_MVB_CHANNEL ),
        .DMA_TX_MVB_HDR_META (DMA_TX_MVB_HDR_META),
        .DMA_TX_MVB_VLD      (DMA_TX_MVB.VLD     ),
        .DMA_TX_MVB_SRC_RDY  (DMA_TX_MVB.SRC_RDY ),
        .DMA_TX_MVB_DST_RDY  (DMA_TX_MVB.DST_RDY ),

        .DMA_TX_MFB_DATA     (DMA_TX_MFB.DATA    ),
        .DMA_TX_MFB_SOF      (DMA_TX_MFB.SOF     ),
        .DMA_TX_MFB_EOF      (DMA_TX_MFB.EOF     ),
        .DMA_TX_MFB_SOF_POS  (DMA_TX_MFB.SOF_POS ),
        .DMA_TX_MFB_EOF_POS  (DMA_TX_MFB.EOF_POS ),
        .DMA_TX_MFB_SRC_RDY  (DMA_TX_MFB.SRC_RDY ),
        .DMA_TX_MFB_DST_RDY  (DMA_TX_MFB.DST_RDY )
    );

    generate

        assign {>>{arr_ETH_RX_MVB_DATA}} = ETH_RX_MVB.DATA;
        assign ETH_TX_MVB.DATA           = {>>{arr_ETH_TX_MVB_DATA}};
        assign DMA_RX_MVB.DATA           = {>>{arr_DMA_RX_MVB_DATA}};
        assign {>>{arr_DMA_TX_MVB_DATA}} = DMA_TX_MVB.DATA;

        for(genvar i = 0; i<REGIONS; i++) begin

            assign {>>{arr_ETH_RX_MVB_LEN[i], arr_ETH_RX_MVB_CHANNEL[i], arr_ETH_RX_MVB_HDR_META[i], arr_ETH_RX_MVB_DISCARD[i]}} = arr_ETH_RX_MVB_DATA[i];
            assign arr_ETH_TX_MVB_DATA[i] = {>>{arr_ETH_TX_MVB_LEN[i], arr_ETH_TX_MVB_CHANNEL[i], arr_ETH_TX_MVB_HDR_META[i]}};
            assign arr_DMA_RX_MVB_DATA[i] = {>>{arr_DMA_RX_MVB_LEN[i], arr_DMA_RX_MVB_CHANNEL[i], arr_DMA_RX_MVB_HDR_META[i], arr_DMA_RX_MVB_DISCARD[i]}};
            assign {>>{arr_DMA_TX_MVB_LEN[i], arr_DMA_TX_MVB_CHANNEL[i], arr_DMA_TX_MVB_HDR_META[i]}} = arr_DMA_TX_MVB_DATA[i];

            //assign arr_ETH_RX_MVB_LEN     [i] = ETH_RX_MVB_DATA[i][log2(PKT_MTU+1)+log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1-1:log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1];
            //assign arr_ETH_RX_MVB_CHANNEL [i] = ETH_RX_MVB_DATA[i][                log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1-1:                      HDR_META_WIDTH+1];
            //assign arr_ETH_RX_MVB_HDR_META[i] = ETH_RX_MVB_DATA[i][                                      HDR_META_WIDTH+1-1:                                     1];
            //assign arr_ETH_RX_MVB_DISCARD [i] = ETH_RX_MVB_DATA[i][                                                     1-1:                                     0];

            //assign arr_ETH_TX_MVB_LEN     [i] = ETH_TX_MVB_DATA[i][log2(PKT_MTU+1)+log2(TX_DMA_CHANNELS)+HDR_META_WIDTH-1:log2(TX_DMA_CHANNELS)+HDR_META_WIDTH];
            //assign arr_ETH_TX_MVB_CHANNEL [i] = ETH_TX_MVB_DATA[i][                log2(TX_DMA_CHANNELS)+HDR_META_WIDTH-1:                      HDR_META_WIDTH];
            //assign arr_ETH_TX_MVB_HDR_META[i] = ETH_TX_MVB_DATA[i][                                      HDR_META_WIDTH-1:                                   0];

            //assign arr_DMA_RX_MVB_LEN     [i] = DMA_RX_MVB_DATA[i][log2(PKT_MTU+1)+log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1-1:log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1];
            //assign arr_DMA_RX_MVB_CHANNEL [i] = DMA_RX_MVB_DATA[i][                log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1-1:                      HDR_META_WIDTH+1];
            //assign arr_DMA_RX_MVB_HDR_META[i] = DMA_RX_MVB_DATA[i][                                      HDR_META_WIDTH+1-1:                                     1];
            //assign arr_DMA_RX_MVB_DISCARD [i] = DMA_RX_MVB_DATA[i][                                                     1-1:                                     0];

            //assign arr_DMA_TX_MVB_LEN     [i] = DMA_TX_MVB_DATA[i][log2(PKT_MTU+1)+log2(TX_DMA_CHANNELS)+HDR_META_WIDTH-1:log2(TX_DMA_CHANNELS)+HDR_META_WIDTH];
            //assign arr_DMA_TX_MVB_CHANNEL [i] = DMA_TX_MVB_DATA[i][                log2(TX_DMA_CHANNELS)+HDR_META_WIDTH-1:                      HDR_META_WIDTH];
            //assign arr_DMA_TX_MVB_HDR_META[i] = DMA_TX_MVB_DATA[i][                                      HDR_META_WIDTH-1:                                   0];

        end

        assign ETH_RX_MVB_LEN      = {>>{arr_ETH_RX_MVB_LEN     }};
        assign ETH_RX_MVB_CHANNEL  = {>>{arr_ETH_RX_MVB_CHANNEL }};
        assign ETH_RX_MVB_HDR_META = {>>{arr_ETH_RX_MVB_HDR_META}};
        assign ETH_RX_MVB_DISCARD  = {>>{arr_ETH_RX_MVB_DISCARD }};

        assign {>>{arr_ETH_TX_MVB_LEN     }} = ETH_TX_MVB_LEN     ;
        assign {>>{arr_ETH_TX_MVB_CHANNEL }} = ETH_TX_MVB_CHANNEL ;
        assign {>>{arr_ETH_TX_MVB_HDR_META}} = ETH_TX_MVB_HDR_META;

        assign {>>{arr_DMA_RX_MVB_LEN     }} = DMA_RX_MVB_LEN     ;
        assign {>>{arr_DMA_RX_MVB_CHANNEL }} = DMA_RX_MVB_CHANNEL ;
        assign {>>{arr_DMA_RX_MVB_HDR_META}} = DMA_RX_MVB_HDR_META;
        assign {>>{arr_DMA_RX_MVB_DISCARD }} = DMA_RX_MVB_DISCARD ;

        assign DMA_TX_MVB_LEN      = {>>{arr_DMA_TX_MVB_LEN     }};
        assign DMA_TX_MVB_CHANNEL  = {>>{arr_DMA_TX_MVB_CHANNEL }};
        assign DMA_TX_MVB_HDR_META = {>>{arr_DMA_TX_MVB_HDR_META}};

    endgenerate

endmodule
