// property.sv: Properties for the Xilinx CMAC interfaces
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

module PROPERTY_CMAC #(
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
    input wire logic CLK_ETH[ETH_PORTS],
    input wire logic CLK_MI,
    input wire logic CLK_MI_PHY,
    input wire logic CLK_MI_PMD,
    input wire logic CLK_TSU,

    reset_if rst_usr,
    reset_if rst_eth[ETH_PORTS],
    reset_if rst_mi,
    reset_if rst_mi_phy,
    reset_if rst_mi_pmd,
    reset_if rst_tsu,

    lbus_if eth_tx[ETH_PORTS],
    lbus_if eth_rx[ETH_PORTS],

    mfb_if usr_rx     [ETH_PORTS],
    mfb_if usr_tx_data[ETH_PORTS],
    mvb_if usr_tx_hdr [ETH_PORTS],

    mi_if mi,     // TODO
    mi_if mi_phy, // TODO
    mi_if mi_pmd, // TODO

    mvb_if tsu
);

    // Shared property
    PROPERTY #(
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
    )
    PROPERTY_BASE (
        .CLK_USR       (CLK_USR   ),
        .CLK_ETH       (CLK_ETH   ),
        .CLK_MI        (CLK_MI    ),
        .CLK_MI_PHY    (CLK_MI_PHY),
        .CLK_MI_PMD    (CLK_MI_PMD),
        .CLK_TSU       (CLK_TSU   ),

        .rst_usr      (rst_usr   ),
        .rst_eth      (rst_eth   ),
        .rst_mi       (rst_mi    ),
        .rst_mi_phy   (rst_mi_phy),
        .rst_mi_pmd   (rst_mi_pmd),
        .rst_tsu      (rst_tsu   ),

        .usr_rx      (usr_rx     ),
        .usr_tx_data (usr_tx_data),
        .usr_tx_hdr  (usr_tx_hdr ),

        .mi     (mi    ),
        .mi_phy (mi_phy),
        .mi_pmd (mi_pmd),

        .tsu (tsu)
    );

    // LBUS properties
    generate;
        for (genvar i = 0; i < ETH_PORTS; i++) begin : gen_i
            lbus_property LBUS_TX_PROPERTY (
                .RESET(rst_eth[i].RESET),
                .vif  (eth_tx [i]      )
            );
            lbus_property LBUS_RX_PROPERTY (
                .RESET(rst_eth[i].RESET),
                .vif  (eth_rx [i]      )
            );
        end
    endgenerate

endmodule
