// dut.sv: Intel E-Tile DUT
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

module DUT #(
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
    input wire logic CLK_ETH[ETH_PORTS],
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

    avst_if.dut_rx eth_rx[ETH_PORTS],
    avst_if.dut_tx eth_tx[ETH_PORTS],

    mfb_if.dut_rx usr_rx     [ETH_PORTS],
    mfb_if.dut_tx usr_tx_data[ETH_PORTS],
    mvb_if.dut_tx usr_tx_hdr [ETH_PORTS],

    mi_if.dut_slave mi,
    mi_if.dut_slave mi_phy,
    mi_if.dut_slave mi_pmd,

    mvb_if.dut_rx tsu
);
    localparam AVST_WIDTH = ETH_PORT_CHAN[0]*REGION_SIZE*BLOCK_SIZE;

    DUT_BASE #(
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
        .ETH_TX_HDR_WIDTH (ETH_TX_HDR_WIDTH ),
        .ETH_RX_HDR_WIDTH (ETH_RX_HDR_WIDTH ),
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
    ) DUT_BASE_U (
        .CLK_USR    (CLK_USR   ),
        .CLK_MI     (CLK_MI    ),
        .CLK_MI_PHY (CLK_MI_PHY),
        .CLK_MI_PMD (CLK_MI_PMD),
        .CLK_TSU    (CLK_TSU   ),

        .rst_usr    (rst_usr   ),
        .rst_eth    (rst_eth   ),
        .rst_mi     (rst_mi    ),
        .rst_mi_phy (rst_mi_phy),
        .rst_mi_pmd (rst_mi_pmd),
        .rst_tsu    (rst_tsu   ),

        .usr_rx      (usr_rx     ),
        .usr_tx_data (usr_tx_data),
        .usr_tx_hdr  (usr_tx_hdr ),

        .mi     (mi    ),
        .mi_phy (mi_phy),
        .mi_pmd (mi_pmd),

        .tsu (tsu)
    );

    generate;
        for (genvar eth_it = 0; eth_it < ETH_PORTS; eth_it++) begin
            logic [AVST_WIDTH*ITEM_WIDTH-1 : 0] avst_data;

            // RX
            for (genvar data_it = 0; data_it < AVST_WIDTH; data_it++) begin
                assign avst_data[(AVST_WIDTH -data_it)*ITEM_WIDTH-1 -: ITEM_WIDTH] = eth_rx[eth_it].DATA[(data_it+1)*ITEM_WIDTH-1 -: ITEM_WIDTH];
            end
            assign DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.rx_avst_data  = avst_data;
            assign DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.rx_avst_error = eth_rx[eth_it].META;
            assign DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.rx_avst_empty = eth_rx[eth_it].EMPTY;
            assign DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.rx_avst_sop   = eth_rx[eth_it].SOP;
            assign DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.rx_avst_eop   = eth_rx[eth_it].EOP;
            assign DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.rx_avst_valid = eth_rx[eth_it].VALID;
            assign eth_rx[eth_it].READY = 1'b1; // it have to be allways ready

            // TX
            for (genvar data_it = 0; data_it < AVST_WIDTH; data_it++) begin
                assign eth_tx[eth_it].DATA[(data_it+1)*ITEM_WIDTH-1 -: ITEM_WIDTH]
                            = DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.tx_avst_data[(AVST_WIDTH -data_it)*ITEM_WIDTH-1 -: ITEM_WIDTH];
            end
            assign eth_tx[eth_it].META  = DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.tx_avst_error;
            assign eth_tx[eth_it].EMPTY = DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.tx_avst_empty;
            assign eth_tx[eth_it].SOP   = DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.tx_avst_sop;
            assign eth_tx[eth_it].EOP   = DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.tx_avst_eop;
            assign eth_tx[eth_it].VALID = DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.tx_avst_valid;
            assign DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.tx_avst_ready[0] = eth_tx[eth_it].READY;

            // CLK
            assign DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.etile_clk_out_vec[0] = CLK_ETH[eth_it];
        end
    endgenerate

endmodule
