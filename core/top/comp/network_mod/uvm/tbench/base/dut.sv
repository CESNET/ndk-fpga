// dut.sv: Base DUT
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

module DUT_BASE #(
    string       ETH_CORE_ARCH,
    int unsigned ETH_PORTS,
    int unsigned ETH_PORT_SPEED[ETH_PORTS-1 : 0],

    int unsigned ETH_PORT_CHAN  [ETH_PORTS-1 : 0],
    int unsigned EHIP_PORT_TYPE [ETH_PORTS-1 : 0],
    int unsigned ETH_PORT_RX_MTU[ETH_PORTS-1 : 0],
    int unsigned ETH_PORT_TX_MTU[ETH_PORTS-1 : 0],

    int unsigned LANES,

    int unsigned QSFP_PORTS,
    int unsigned QSFP_I2C_PORTS,
    int unsigned QSFP_I2C_TRISTATE,

    int unsigned ETH_TX_HDR_WIDTH,
    int unsigned ETH_RX_HDR_WIDTH,

    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,

    int unsigned MI_DATA_WIDTH,
    int unsigned MI_ADDR_WIDTH,

    int unsigned MI_DATA_WIDTH_PHY,
    int unsigned MI_ADDR_WIDTH_PHY,

    int unsigned LANE_RX_POLARITY,
    int unsigned LANE_TX_POLARITY,

    int unsigned RESET_WIDTH,

    string DEVICE,
    string BOARD
)(
    input wire logic CLK_USR,
    input wire logic CLK_MI,
    input wire logic CLK_MI_PHY,
    input wire logic CLK_MI_PMD,
    input wire logic CLK_TSU,

    reset_if.dut rst_usr,
    reset_if.dut rst_eth[ETH_PORTS],
    reset_if.dut rst_mi,
    reset_if.dut rst_mi_phy,
    reset_if.dut rst_mi_pmd,
    reset_if.dut rst_tsu,

    mfb_if.dut_rx usr_rx     [ETH_PORTS],
    mfb_if.dut_tx usr_tx_data[ETH_PORTS],
    mvb_if.dut_tx usr_tx_hdr [ETH_PORTS],

    mi_if.dut_slave mi,
    mi_if.dut_slave mi_phy,
    mi_if.dut_slave mi_pmd,

    mvb_if.dut_rx tsu
);
    wire logic [RESET_WIDTH-1 : 0] reset_user;
    wire logic [ETH_PORTS  -1 : 0] reset_eth;

    //USR RX
    wire logic [ETH_PORTS*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1:0]  usr_rx_data;
    wire logic [ETH_PORTS*REGIONS*ETH_TX_HDR_WIDTH-1:0]       usr_rx_hdr;
    wire logic [ETH_PORTS*REGIONS-1:0]                        usr_rx_sof;
    wire logic [ETH_PORTS*REGIONS-1:0]                        usr_rx_eof;
    wire logic [ETH_PORTS*REGIONS*$clog2(REGION_SIZE)-1:0]            usr_rx_sof_pos;
    wire logic [ETH_PORTS*REGIONS*$clog2(REGION_SIZE*BLOCK_SIZE)-1:0] usr_rx_eof_pos;
    wire logic [ETH_PORTS-1:0]                                usr_rx_src_rdy;
    wire logic [ETH_PORTS-1:0]                                usr_rx_dst_rdy;

    //USR TX
    wire logic [ETH_PORTS*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1:0] usr_tx_data_data;
    wire logic [ETH_PORTS*REGIONS-1:0]                        usr_tx_data_sof;
    wire logic [ETH_PORTS*REGIONS-1:0]                        usr_tx_data_eof;
    wire logic [ETH_PORTS*REGIONS*$clog2(REGION_SIZE)-1:0]            usr_tx_data_sof_pos;
    wire logic [ETH_PORTS*REGIONS*$clog2(REGION_SIZE*BLOCK_SIZE)-1:0] usr_tx_data_eof_pos;
    wire logic [ETH_PORTS-1:0]                                usr_tx_data_src_rdy;
    wire logic [ETH_PORTS-1:0]                                usr_tx_data_dst_rdy;

    wire logic [ETH_PORTS*REGIONS*ETH_RX_HDR_WIDTH-1:0]       usr_tx_hdr_data;
    wire logic [ETH_PORTS*REGIONS-1:0]                        usr_tx_hdr_vld;
    wire logic [ETH_PORTS-1:0]                                usr_tx_hdr_src_rdy;
    wire logic [ETH_PORTS-1:0]                                usr_tx_hdr_dst_rdy;

    for (genvar rst_it = 0; rst_it < RESET_WIDTH; rst_it++) begin
        assign reset_user[rst_it] = rst_usr.RESET;
    end

    for (genvar eth_it = 0; eth_it < ETH_PORTS; eth_it++) begin
        //RESET
        assign reset_eth[eth_it] = rst_eth[eth_it].RESET;

        //RX
        assign usr_rx_data[(eth_it+1)*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH -1 -: REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH] = usr_rx[eth_it].DATA;
        assign usr_rx_hdr[(eth_it+1)*REGIONS*ETH_TX_HDR_WIDTH -1 -: REGIONS*ETH_TX_HDR_WIDTH]                                    = usr_rx[eth_it].META;
        assign usr_rx_sof[(eth_it+1)*REGIONS -1 -: REGIONS]                                                                      = usr_rx[eth_it].SOF;
        assign usr_rx_eof[(eth_it+1)*REGIONS -1 -: REGIONS]                                                                      = usr_rx[eth_it].EOF;
        assign usr_rx_sof_pos[(eth_it+1)*REGIONS*$clog2(REGION_SIZE) -1 -: REGIONS*$clog2(REGION_SIZE)]                          = usr_rx[eth_it].SOF_POS;
        assign usr_rx_eof_pos[(eth_it+1)*REGIONS*$clog2(REGION_SIZE*BLOCK_SIZE) -1 -: REGIONS*$clog2(REGION_SIZE*BLOCK_SIZE)]    = usr_rx[eth_it].EOF_POS;
        assign usr_rx_src_rdy[eth_it]                                                                                            = usr_rx[eth_it].SRC_RDY;
        assign usr_rx[eth_it].DST_RDY                                                                                            = usr_rx_dst_rdy[eth_it];

        //TX
        assign usr_tx_data[eth_it].DATA    = usr_tx_data_data[(eth_it+1)*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH -1 -: REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH];
        assign usr_tx_data[eth_it].SOF     = usr_tx_data_sof[(eth_it+1)*REGIONS -1 -: REGIONS];
        assign usr_tx_data[eth_it].EOF     = usr_tx_data_eof[(eth_it+1)*REGIONS -1 -: REGIONS];
        assign usr_tx_data[eth_it].SOF_POS = usr_tx_data_sof_pos[(eth_it+1)*REGIONS*$clog2(REGION_SIZE) -1 -: REGIONS*$clog2(REGION_SIZE)];
        assign usr_tx_data[eth_it].EOF_POS = usr_tx_data_eof_pos[(eth_it+1)*REGIONS*$clog2(REGION_SIZE*BLOCK_SIZE) -1 -: REGIONS*$clog2(REGION_SIZE*BLOCK_SIZE)];
        assign usr_tx_data[eth_it].SRC_RDY = usr_tx_data_src_rdy[eth_it];
        assign usr_tx_data_dst_rdy[eth_it] = usr_tx_data[eth_it].DST_RDY;

        assign usr_tx_hdr[eth_it].DATA    = usr_tx_hdr_data   [(eth_it+1)*REGIONS*ETH_RX_HDR_WIDTH-1 -: REGIONS*ETH_RX_HDR_WIDTH];
        assign usr_tx_hdr[eth_it].VLD     = usr_tx_hdr_vld    [(eth_it+1)*REGIONS-1 -: REGIONS];
        assign usr_tx_hdr[eth_it].SRC_RDY = usr_tx_hdr_src_rdy[eth_it];
        assign usr_tx_hdr_dst_rdy[eth_it] = usr_tx_hdr[eth_it].DST_RDY;
    end

    NETWORK_MOD #(
        .ETH_CORE_ARCH    (ETH_CORE_ARCH    ),
        .ETH_PORTS        (ETH_PORTS        ),
        .ETH_PORT_SPEED   (ETH_PORT_SPEED   ),

        .ETH_PORT_CHAN    (ETH_PORT_CHAN    ),
        .EHIP_PORT_TYPE   (EHIP_PORT_TYPE   ),
        .ETH_PORT_RX_MTU  (ETH_PORT_RX_MTU  ),
        .ETH_PORT_TX_MTU  (ETH_PORT_TX_MTU  ),
        .LANES            (LANES            ),
        .QSFP_PORTS       (QSFP_PORTS       ),
        .QSFP_I2C_PORTS   (QSFP_I2C_PORTS   ),
        .QSFP_I2C_TRISTATE(QSFP_I2C_TRISTATE),

        .REGIONS          (REGIONS          ),
        .REGION_SIZE      (REGION_SIZE      ),
        .BLOCK_SIZE       (BLOCK_SIZE       ),
        .ITEM_WIDTH       (ITEM_WIDTH       ),

        .MI_DATA_WIDTH    (MI_DATA_WIDTH    ),
        .MI_ADDR_WIDTH    (MI_ADDR_WIDTH    ),

        .MI_DATA_WIDTH_PHY(MI_DATA_WIDTH_PHY),
        .MI_ADDR_WIDTH_PHY(MI_ADDR_WIDTH_PHY),

        .LANE_RX_POLARITY (LANE_RX_POLARITY ),
        .LANE_TX_POLARITY (LANE_TX_POLARITY ),
        .RESET_WIDTH      (RESET_WIDTH      ),
        .DEVICE           (DEVICE           ),
        .BOARD            (BOARD            )
    )
    VHDL_DUT_U (
        .CLK_USER       (CLK_USR),
        .CLK_ETH        (),

        .RESET_USER     (reset_user),
        .RESET_ETH      (reset_eth),

        .ETH_REFCLK_P   (),
        .ETH_REFCLK_N   (),
        .ETH_RX_P       (),
        .ETH_RX_N       (),
        .ETH_TX_P       (),
        .ETH_TX_N       (),

        .QSFP_I2C_SCL   (),
        .QSFP_I2C_SDA   (),
        .QSFP_I2C_SDA_I (),
        .QSFP_I2C_SCL_I (),
        .QSFP_I2C_SCL_O (),
        .QSFP_I2C_SCL_OE(),
        .QSFP_I2C_SDA_O (),
        .QSFP_I2C_SDA_OE(),
        .QSFP_I2C_DIR   (),
        .QSFP_MODSEL_N  (),
        .QSFP_LPMODE    (),
        .QSFP_RESET_N   (),
        .QSFP_MODPRS_N  (),
        .QSFP_INT_N     (),


        .ACTIVITY_RX    (),
        .ACTIVITY_TX    (),
        .RX_LINK_UP     (),
        .TX_LINK_UP     (),

        .RX_MFB_DATA    (usr_rx_data),
        .RX_MFB_HDR     (usr_rx_hdr),
        .RX_MFB_SOF     (usr_rx_sof),
        .RX_MFB_EOF     (usr_rx_eof),
        .RX_MFB_SOF_POS (usr_rx_sof_pos),
        .RX_MFB_EOF_POS (usr_rx_eof_pos),
        .RX_MFB_SRC_RDY (usr_rx_src_rdy),
        .RX_MFB_DST_RDY (usr_rx_dst_rdy),

        .TX_MFB_DATA    (usr_tx_data_data),
        .TX_MFB_SOF     (usr_tx_data_sof),
        .TX_MFB_EOF     (usr_tx_data_eof),
        .TX_MFB_SOF_POS (usr_tx_data_sof_pos),
        .TX_MFB_EOF_POS (usr_tx_data_eof_pos),
        .TX_MFB_SRC_RDY (usr_tx_data_src_rdy),
        .TX_MFB_DST_RDY (usr_tx_data_dst_rdy),

        .TX_MVB_DATA    (usr_tx_hdr_data),
        .TX_MVB_VLD     (usr_tx_hdr_vld),
        .TX_MVB_SRC_RDY (usr_tx_hdr_src_rdy),
        .TX_MVB_DST_RDY (usr_tx_hdr_dst_rdy),

        .MI_CLK         (CLK_MI),
        .MI_RESET       (rst_mi.RESET),
        .MI_DWR         (mi.DWR),
        .MI_ADDR        (mi.ADDR),
        .MI_RD          (mi.RD),
        .MI_WR          (mi.WR),
        .MI_BE          (mi.BE),
        .MI_DRD         (mi.DRD),
        .MI_ARDY        (mi.ARDY),
        .MI_DRDY        (mi.DRDY),

        .MI_CLK_PHY     (CLK_MI_PHY),
        .MI_RESET_PHY   (rst_mi_phy.RESET),
        .MI_DWR_PHY     (mi_phy.DWR),
        .MI_ADDR_PHY    (mi_phy.ADDR),
        .MI_RD_PHY      (mi_phy.RD),
        .MI_WR_PHY      (mi_phy.WR),
        .MI_BE_PHY      (mi_phy.BE),
        .MI_DRD_PHY     (mi_phy.DRD),
        .MI_ARDY_PHY    (mi_phy.ARDY),
        .MI_DRDY_PHY    (mi_phy.DRDY),

        .MI_CLK_PMD     (CLK_MI_PMD),
        .MI_RESET_PMD   (rst_mi_pmd.RESET),
        .MI_DWR_PMD     (mi_pmd.DWR),
        .MI_ADDR_PMD    (mi_pmd.ADDR),
        .MI_RD_PMD      (mi_pmd.RD),
        .MI_WR_PMD      (mi_pmd.WR),
        .MI_BE_PMD      (mi_pmd.BE),
        .MI_DRD_PMD     (mi_pmd.DRD),
        .MI_ARDY_PMD    (mi_pmd.ARDY),
        .MI_DRDY_PMD    (mi_pmd.DRDY),

        .TSU_CLK        (CLK_TSU),
        .TSU_RST        (rst_tsu.RESET),
        .TSU_TS_NS      (tsu.DATA),
        .TSU_TS_DV      (tsu.SRC_RDY & tsu.VLD[0])
        //.TSU_TS_DV      (1'b1)
    );
    assign tsu.DST_RDY = 1'b1;

endmodule
