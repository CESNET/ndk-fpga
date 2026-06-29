// testbench.sv: Testbench for Xilinx CMAC
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"

import test::*;

module testbench;

    // --------------------- //
    // Test type definitions //
    // --------------------- //

    typedef test::base  #(
        .ETH_CORE_ARCH    (ETH_CORE_ARCH    ),
        .ETH_PORTS        (ETH_PORTS        ),
        .ETH_PORT_SPEED   (ETH_PORT_SPEED   ),
        .ETH_PORT_CHAN    (ETH_PORT_CHAN    ),
        .ETH_TX_HDR_WIDTH (ETH_TX_HDR_WIDTH ),
        .ETH_RX_HDR_WIDTH (ETH_RX_HDR_WIDTH ),
        .REGIONS          (REGIONS          ),
        .REGION_SIZE      (REGION_SIZE      ),
        .BLOCK_SIZE       (BLOCK_SIZE       ),
        .ITEM_WIDTH       (ITEM_WIDTH       ),
        .MI_DATA_WIDTH    (MI_DATA_WIDTH    ),
        .MI_ADDR_WIDTH    (MI_ADDR_WIDTH    )
    ) base;
    typedef test::speed #(
        .ETH_CORE_ARCH    (ETH_CORE_ARCH    ),
        .ETH_PORTS        (ETH_PORTS        ),
        .ETH_PORT_SPEED   (ETH_PORT_SPEED   ),
        .ETH_PORT_CHAN    (ETH_PORT_CHAN    ),
        .ETH_TX_HDR_WIDTH (ETH_TX_HDR_WIDTH ),
        .ETH_RX_HDR_WIDTH (ETH_RX_HDR_WIDTH ),
        .REGIONS          (REGIONS          ),
        .REGION_SIZE      (REGION_SIZE      ),
        .BLOCK_SIZE       (BLOCK_SIZE       ),
        .ITEM_WIDTH       (ITEM_WIDTH       ),
        .MI_DATA_WIDTH    (MI_DATA_WIDTH    ),
        .MI_ADDR_WIDTH    (MI_ADDR_WIDTH    )
    ) speed;

    // ------ //
    // Clocks //
    // ------ //

    logic CLK_USR            = 0;
    logic CLK_ETH[ETH_PORTS];
    logic CLK_MI             = 0;
    logic CLK_MI_PHY         = 0;
    logic CLK_MI_PMD         = 0;
    logic CLK_TSU            = 0;

    // ------ //
    // Resets //
    // ------ //

    reset_if rst_usr           (CLK_USR);
    pullup(rst_usr.RESET);
    reset_if rst_eth[ETH_PORTS](CLK_ETH[0]);
    for (genvar eth_it = 0; eth_it < ETH_PORTS; eth_it++) begin : rst_gen
        pullup(rst_eth[eth_it].RESET);
    end
    reset_if rst_mi            (CLK_MI);
    pullup(rst_mi.RESET);
    reset_if rst_mi_phy        (CLK_MI_PHY);
    pullup(rst_mi_phy.RESET);
    reset_if rst_mi_pmd        (CLK_MI_PMD);
    pullup(rst_mi_pmd.RESET);
    reset_if rst_tsu           (CLK_TSU);
    pullup(rst_tsu.RESET);

    // ---------- //
    // Interfaces //
    // ---------- //

    lbus_if eth_tx[ETH_PORTS](CLK_ETH);
    lbus_if eth_rx[ETH_PORTS](CLK_ETH);

    mfb_if #(
        .REGIONS (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE (BLOCK_SIZE),
        .ITEM_WIDTH (ITEM_WIDTH),
        .META_WIDTH (ETH_TX_HDR_WIDTH)
    ) usr_rx     [ETH_PORTS](CLK_USR);
    mfb_if #(
        .REGIONS (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE (BLOCK_SIZE),
        .ITEM_WIDTH (ITEM_WIDTH),
        .META_WIDTH (0)
    )                usr_tx_data[ETH_PORTS](CLK_USR);
    mvb_if #(
        .ITEMS (REGIONS),
        .ITEM_WIDTH (ETH_RX_HDR_WIDTH)
    )                                      usr_tx_hdr [ETH_PORTS](CLK_USR);

    mi_if #(
        .DATA_WIDTH (MI_DATA_WIDTH),
        .ADDR_WIDTH (MI_ADDR_WIDTH)
    ) mi    (CLK_MI);
    mi_if #(
        .DATA_WIDTH (MI_DATA_WIDTH),
        .ADDR_WIDTH (MI_ADDR_WIDTH)
    ) mi_phy(CLK_MI_PHY);
    mi_if #(
        .DATA_WIDTH (MI_DATA_WIDTH),
        .ADDR_WIDTH (MI_ADDR_WIDTH)
    ) mi_pmd(CLK_MI_PMD);

    mvb_if #(
        .ITEMS (1),
        .ITEM_WIDTH (64)
    ) tsu(CLK_TSU);

    // Fix bind
    fix_bind #(
        .PORTS    (ETH_PORTS),
        .CHANNELS (ETH_PORT_CHAN[0])
    ) bind_i();

    // ------------------------- //
    // Clock ticking definitions //
    // ------------------------- //

    always begin
        #(CLK_USR_PERIOD/2) CLK_USR = ~CLK_USR;
    end
    always begin
        #(CLK_MI_PERIOD/2) CLK_MI     = ~CLK_MI    ;
    end
    always begin
        #(CLK_MI_PHY_PERIOD/2) CLK_MI_PHY = ~CLK_MI_PHY;
    end
    always begin
        #(CLK_MI_PMD_PERIOD/2) CLK_MI_PMD = ~CLK_MI_PMD;
    end
    always begin
        #(CLK_TSU_PERIOD/2) CLK_TSU    = ~CLK_TSU   ;
    end

    initial begin
        // --------- //
        // Variables //
        // --------- //

        automatic uvm_root m_root;

        automatic virtual reset_if vif_rst_eth[ETH_PORTS] = rst_eth;
        automatic virtual mfb_if #(
            .REGIONS (REGIONS),
            .REGION_SIZE (REGION_SIZE),
            .BLOCK_SIZE (BLOCK_SIZE),
            .ITEM_WIDTH (ITEM_WIDTH),
            .META_WIDTH (ETH_TX_HDR_WIDTH)
        ) vif_usr_rx     [ETH_PORTS] = usr_rx;
        automatic virtual mfb_if #(
            .REGIONS (REGIONS),
            .REGION_SIZE (REGION_SIZE),
            .BLOCK_SIZE (BLOCK_SIZE),
            .ITEM_WIDTH (ITEM_WIDTH),
            .META_WIDTH (0)
        )                vif_usr_tx_data[ETH_PORTS] = usr_tx_data;
        automatic virtual mvb_if #(
            .ITEMS (REGIONS),
            .ITEM_WIDTH (ETH_RX_HDR_WIDTH)
        )                                      vif_usr_tx_hdr [ETH_PORTS] = usr_tx_hdr;
        automatic virtual lbus_if                                                                  vif_eth_tx     [ETH_PORTS] = eth_tx;
        automatic virtual lbus_if                                                                  vif_eth_rx     [ETH_PORTS] = eth_rx;

        // ------------- //
        // Configuration //
        // ------------- //

        // Setting of interfaces
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_rst_usr", rst_usr);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            uvm_config_db#(virtual reset_if)::set(null, "", $sformatf("vif_rst_eth_%0d", it), vif_rst_eth[it]);
        end
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_rst_mi", rst_mi);
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_rst_mi_phy", rst_mi_phy);
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_rst_mi_pmd", rst_mi_pmd);
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_rst_tsu", rst_tsu);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            uvm_config_db#(virtual mfb_if #(
                .REGIONS (REGIONS),
                .REGION_SIZE (REGION_SIZE),
                .BLOCK_SIZE (BLOCK_SIZE),
                .ITEM_WIDTH (ITEM_WIDTH),
                .META_WIDTH (ETH_TX_HDR_WIDTH)
            ))::set(null, "", $sformatf("vif_usr_rx_%0d", it)     , vif_usr_rx[it]);
            uvm_config_db#(virtual mfb_if #(
                .REGIONS (REGIONS),
                .REGION_SIZE (REGION_SIZE),
                .BLOCK_SIZE (BLOCK_SIZE),
                .ITEM_WIDTH (ITEM_WIDTH),
                .META_WIDTH (0)
            )                             )::set(null, "", $sformatf("vif_usr_tx_data_%0d", it), vif_usr_tx_data[it]);
            uvm_config_db#(virtual mvb_if #(
                .ITEMS (REGIONS),
                .ITEM_WIDTH (ETH_RX_HDR_WIDTH)
            )                                                                               )::set(null, "", $sformatf("vif_usr_tx_hdr_%0d", it) , vif_usr_tx_hdr[it]);

            uvm_config_db#(virtual lbus_if)::set(null, "", $sformatf("vif_eth_tx_%0d", it) , vif_eth_tx[it]);
            uvm_config_db#(virtual lbus_if)::set(null, "", $sformatf("vif_eth_rx_%0d", it) , vif_eth_rx[it]);
        end
        uvm_config_db#(virtual mi_if #(
            .DATA_WIDTH (MI_DATA_WIDTH),
            .ADDR_WIDTH (MI_ADDR_WIDTH)
        ))::set(null, "", "vif_mi"    , mi);
        uvm_config_db#(virtual mi_if #(
            .DATA_WIDTH (MI_DATA_WIDTH),
            .ADDR_WIDTH (MI_ADDR_WIDTH)
        ))::set(null, "", "vif_mi_phy", mi_phy);
        uvm_config_db#(virtual mi_if #(
            .DATA_WIDTH (MI_DATA_WIDTH),
            .ADDR_WIDTH (MI_ADDR_WIDTH)
        ))::set(null, "", "vif_mi_pmd", mi_pmd);
        uvm_config_db#(virtual mvb_if #(
            .ITEMS (1),
            .ITEM_WIDTH (64)
        ))::set(null, "", "vif_tsu", tsu);

        // Configuration of the database
        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME", UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        // Instance override
        uvm_network_mod_env::env #(
            .ETH_CORE_ARCH    (ETH_CORE_ARCH    ),
            .ETH_PORTS        (ETH_PORTS        ),
            .ETH_PORT_SPEED   (ETH_PORT_SPEED   ),
            .ETH_PORT_CHAN    (ETH_PORT_CHAN    ),
            .ETH_TX_HDR_WIDTH (ETH_TX_HDR_WIDTH ),
            .ETH_RX_HDR_WIDTH (ETH_RX_HDR_WIDTH ),
            .REGIONS          (REGIONS          ),
            .REGION_SIZE      (REGION_SIZE      ),
            .BLOCK_SIZE       (BLOCK_SIZE       ),
            .ITEM_WIDTH       (ITEM_WIDTH       ),
            .MI_DATA_WIDTH    (MI_DATA_WIDTH    ),
            .MI_ADDR_WIDTH    (MI_ADDR_WIDTH    )
        )::type_id::set_inst_override(
            uvm_network_mod_cmac_env::env #(
                .ETH_CORE_ARCH    (ETH_CORE_ARCH    ),
                .ETH_PORTS        (ETH_PORTS        ),
                .ETH_PORT_SPEED   (ETH_PORT_SPEED   ),
                .ETH_PORT_CHAN    (ETH_PORT_CHAN    ),
                .ETH_TX_HDR_WIDTH (ETH_TX_HDR_WIDTH ),
                .ETH_RX_HDR_WIDTH (ETH_RX_HDR_WIDTH ),
                .REGIONS          (REGIONS          ),
                .REGION_SIZE      (REGION_SIZE      ),
                .BLOCK_SIZE       (BLOCK_SIZE       ),
                .ITEM_WIDTH       (ITEM_WIDTH       ),
                .MI_DATA_WIDTH    (MI_DATA_WIDTH    ),
                .MI_ADDR_WIDTH    (MI_ADDR_WIDTH    )
            )::get_type(),
            "uvm_test_top.m_env"
        );

        // -------- //
        // Test run //
        // -------- //

        run_test();
        $stop(2);
    end

    // === //
    // DUT //
    // === //

    DUT #(
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
        .ETH_TX_HDR_WIDTH (ETH_TX_HDR_WIDTH),
        .ETH_RX_HDR_WIDTH (ETH_RX_HDR_WIDTH),
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
        .BOARD            (BOARD            ),
        .CLK_ETH_PERIOD   (CLK_ETH_PERIOD   )
    ) DUT_U (
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

        .eth_tx (eth_tx),
        .eth_rx (eth_rx),

        .usr_rx      (usr_rx     ),
        .usr_tx_data (usr_tx_data),
        .usr_tx_hdr  (usr_tx_hdr ),

        .mi     (mi    ),
        .mi_phy (mi_phy),
        .mi_pmd (mi_pmd),

        .tsu (tsu)
    );

    // ========== //
    // Properties //
    // ========== //

    PROPERTY_CMAC #(
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
    PROPERTY_U (
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

        .eth_tx      (eth_tx     ),
        .eth_rx      (eth_rx     ),

        .usr_rx      (usr_rx     ),
        .usr_tx_data (usr_tx_data),
        .usr_tx_hdr  (usr_tx_hdr ),

        .mi     (mi    ),
        .mi_phy (mi_phy),
        .mi_pmd (mi_pmd),

        .tsu (tsu)
    );

endmodule
