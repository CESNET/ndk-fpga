// tbench.sv: Testbench
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kondys <xkondy00@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause 

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Signals
    logic CLK_USER = 0;
    logic CLK_CORE = 0;
    logic MI_CLK = 0;

    logic [RESET_USER_WIDTH-1:0] RESET_USER = '0;
    logic [RESET_CORE_WIDTH-1:0] RESET_CORE = '0;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    // TX path
    mfb_if #(USER_REGIONS, USER_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) user_mfb_rx              (CLK_USER);
    mfb_if #(CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0         ) core_mfb_tx[ETH_CHANNELS](CLK_CORE);
    // RX path
    mfb_if #(CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0         ) core_mfb_rx[ETH_CHANNELS](CLK_CORE);
    mfb_if #(USER_REGIONS, USER_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0         ) user_mfb_tx              (CLK_USER);
    mvb_if #(USER_REGIONS, USER_MVB_WIDTH                                      ) user_mvb_tx              (CLK_USER);
    // MVB discard (monitors discard of RX MAC Lites)
    mvb_if #(RX_MAC_LITE_REGIONS, 1                                            ) mvb_discard[ETH_CHANNELS](CLK_CORE);
    // MI
    mi_if  #(MI_DATA_WIDTH, MI_ADDR_WIDTH                                      ) mi_config(MI_CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(CLK_PERIOD_USER) CLK_USER = ~CLK_USER;
    always #(CLK_PERIOD_CORE) CLK_CORE = ~CLK_CORE;
    always #(CLK_PERIOD_CORE) MI_CLK   = ~MI_CLK;

    reset_if reset(CLK_USER);
    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Initial reset
    initial begin
        RESET_USER = '1;
        RESET_CORE = '1;
        #(RESET_CLKS*CLK_PERIOD_USER) //CLK_PERIOD_USER is longer
        RESET_USER = '0;
        RESET_CORE = '0;
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;
         // Virtual interface for CORE TX inf (because it's an array)
        automatic virtual mfb_if #(CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0) v_core_mfb_tx[ETH_CHANNELS] = core_mfb_tx;
         // Virtual interface for CORE RX inf (because it's an array)
        automatic virtual mfb_if #(CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0) v_core_mfb_rx[ETH_CHANNELS] = core_mfb_rx;
         // Virtual interface for MVB discard inf (because it's an array)
        automatic virtual mvb_if #(RX_MAC_LITE_REGIONS, 1                                   ) v_mvb_discard[ETH_CHANNELS] = mvb_discard;

        // Configuration of database ------------------------------------------
        // TX path
        uvm_config_db#(virtual mfb_if #(USER_REGIONS, USER_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))::set(null, "", "vif_user_rx_mfb", user_mfb_rx);
        for (int unsigned i = 0; i < ETH_CHANNELS; i++ ) begin
            string i_string;
            i_string.itoa(i);
            uvm_config_db#(virtual mfb_if #(CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0))::set(null, "", {"vif_core_tx_mfb_",i_string}, v_core_mfb_tx[i]);
        end

        // RX path
        for (int unsigned i = 0; i < ETH_CHANNELS; i++ ) begin
            string i_string;
            i_string.itoa(i);
            uvm_config_db#(virtual mfb_if #(CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0))::set(null, "", {"vif_core_rx_mfb_",i_string}, v_core_mfb_rx[i]);
        end
        uvm_config_db#(virtual mfb_if #(USER_REGIONS, USER_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0))::set(null, "", "vif_user_tx_mfb", user_mfb_tx);
        uvm_config_db#(virtual mvb_if #(USER_REGIONS, USER_MVB_WIDTH                             ))::set(null, "", "vif_user_tx_mvb", user_mvb_tx);

        // MVB tap on discard
        for (int unsigned i = 0; i < ETH_CHANNELS; i++ ) begin
            string i_string;
            i_string.itoa(i);
            uvm_config_db#(virtual mvb_if #(RX_MAC_LITE_REGIONS, 1))::set(null, "", {"vif_mvb_discard_",i_string}, v_mvb_discard[i]);
        end

        // MI
        uvm_config_db#(virtual mi_if#(MI_DATA_WIDTH, MI_ADDR_WIDTH))::set(null, "", "MI_INTERFACE", mi_config);
        // --------------------------------------------------------------------

        m_root = uvm_root::get();
        //m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        run_test();
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // DUT
    DUT DUT_U (
        .CLK_USER   (CLK_USER),
        .CLK_CORE   (CLK_CORE),
        .MI_CLK     (MI_CLK),

        .RESET_USER (RESET_USER),
        .RESET_CORE (RESET_CORE),

        // TX path
        .user_mfb_rx (user_mfb_rx),
        .core_mfb_tx (core_mfb_tx),
        // RX path
        .core_mfb_rx (core_mfb_rx),
        .user_mfb_tx (user_mfb_tx),
        .user_mvb_tx (user_mvb_tx),

        // MVB discard inf
        .mvb_discard (mvb_discard),

        .mi_config   (mi_config)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Properties

endmodule
