// dut.sv: Xilinx CMAC DUT
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
    string BOARD,
    time CLK_ETH_PERIOD[ETH_PORTS]
)(
    output wire logic CLK_ETH[ETH_PORTS],
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

    lbus_if.dut_tx eth_tx[ETH_PORTS],
    lbus_if.dut_rx eth_rx[ETH_PORTS],

    mfb_if.dut_rx usr_rx     [ETH_PORTS],
    mfb_if.dut_tx usr_tx_data[ETH_PORTS],
    mvb_if.dut_tx usr_tx_hdr [ETH_PORTS],

    mi_if.dut_slave mi,
    mi_if.dut_slave mi_phy,
    mi_if.dut_slave mi_pmd,

    mvb_if.dut_rx tsu
);
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
        .CLK_ETH    (CLK_ETH   ),
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
            localparam int unsigned ETH_PORT_CHAN_LOCAL = ETH_PORT_CHAN[eth_it];
            initial assert(ETH_PORT_CHAN_LOCAL == 1);

            logic CLK_ETH_GEN = 1'b0;

            always #(CLK_ETH_PERIOD[eth_it]/2) CLK_ETH_GEN = ~CLK_ETH_GEN;

            // ------- //
            // TX side //
            // ------- //

            for (genvar slice = 0; slice < 4; slice++) begin
                initial begin
                    force DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.cmac_rx_lbus_data[slice] = eth_tx[eth_it].DATA[128*(slice+1)-1 -: 128]; // Byte reordering
                    force DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.cmac_rx_lbus_mty [slice] = eth_tx[eth_it].MTY[4*(slice+1)-1 -: 4];
                end
            end

            initial begin
                force DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.cmac_rx_lbus_ena = eth_tx[eth_it].ENA;
                force DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.cmac_rx_lbus_sop = eth_tx[eth_it].SOP;
                force DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.cmac_rx_lbus_eop = eth_tx[eth_it].EOP;
                force DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.cmac_rx_lbus_err = eth_tx[eth_it].ERR;
            end

            assign eth_tx[eth_it].RDY = 1'b1; // Always ready

            // ------- //
            // RX side //
            // ------- //

            for (genvar segment = 0; segment < 4; segment++) begin
                assign eth_rx[eth_it].DATA[128*(segment+1)-1 -: 128] = DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.cmac_tx_lbus_data[segment]; // Byte reordering
                assign eth_rx[eth_it].MTY[4*(segment+1)-1 -: 4]      = DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.cmac_tx_lbus_mty[segment];
            end

            assign eth_rx[eth_it].ENA = DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.cmac_tx_lbus_ena;
            assign eth_rx[eth_it].SOP = DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.cmac_tx_lbus_sop;
            assign eth_rx[eth_it].EOP = DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.cmac_tx_lbus_eop;
            assign eth_rx[eth_it].ERR = DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.cmac_tx_lbus_err;

            initial force DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.cmac_tx_lbus_rdy = eth_rx[eth_it].RDY;

            // ----- //
            // Other //
            // ----- //

            // CLK connection
            initial force DUT_BASE_U.VHDL_DUT_U.eth_core_g[eth_it].network_mod_core_i.cmac_gt_tx_clk_322m = CLK_ETH_GEN;
        end
    endgenerate

endmodule
