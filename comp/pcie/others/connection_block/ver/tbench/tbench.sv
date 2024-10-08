/* tbench.sv: top modul of functional verification connection_block
 * Copyright (C) 2020 CESNET
 * Author: Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

`include "uvm_macros.svh"
import uvm_pkg::*;
import test::*;

module testbench;

   timeunit      1ns;
   timeprecision 1ps;

    logic CLK = 0;
    logic RESET = 0;

    //AVALON
    avst_tx_if #(env::REGIONS)      pce_avalon_tx(CLK, RESET);
    avst_rx_if #(env::REGIONS)      pce_avalon_rx(CLK, RESET);

    //PTC MFB
    iMfbRx #(2, 1, 8, 32, 32+128)   ptc_mfb_rx(CLK, RESET);
    iMfbTx #(2, 1, 8, 32, 3+32+128) ptc_mfb_tx(CLK, RESET);

    //MI MFB
    iMfbRx #(2, 1, 8, 32, 32+128)   mi_mfb_rx(CLK, RESET);
    iMfbTx #(2, 1, 8, 32, 3+32+128) mi_mfb_tx(CLK, RESET);

    always #(2ns) CLK = ~CLK;

    //set RESET TO ZERO
    initial begin
        RESET = 1;
        #(10ns) RESET = 0;
    end

    ////////////////////////
    // program
    initial
    begin
        avst_tx::config_item #(env::REGIONS) avalon_tx_cfg;
        avst_rx::config_item #(env::REGIONS) avalon_rx_cfg;

        //setup avalon tx
        avalon_tx_cfg = new("avalon_tx_config");
        avalon_tx_cfg.vif = pce_avalon_tx;
        uvm_config_db #(avst_tx::config_item#(env::REGIONS))::set(null, "uvm_test_top.m_env.m_avalon_tx_env.m_avst_agent", "config", avalon_tx_cfg);
        //setup avalon rx
        avalon_rx_cfg = new("avalon_rx_config");
        avalon_rx_cfg.vif = pce_avalon_rx;
        uvm_config_db #(avst_rx::config_item#(env::REGIONS))::set(null, "uvm_test_top.m_env.m_avalon_rx_env.m_avst_agent", "config", avalon_rx_cfg);
        //setup PCT
        uvm_config_db #(virtual iMfbRx #(2, 1, 8, 32, 32+128))::set  (null, "uvm_test_top.m_env.m_mfb_rx_agent_ptc", "vif", ptc_mfb_rx);
        uvm_config_db #(virtual iMfbTx #(2, 1, 8, 32, 3+32+128))::set(null, "uvm_test_top.m_env.m_mfb_tx_agent_ptc", "vif", ptc_mfb_tx);
        //setup PCT
        uvm_config_db #(virtual iMfbRx #(2, 1, 8, 32, 32+128))::set  (null, "uvm_test_top.m_env.m_mfb_rx_agent_mi", "vif", mi_mfb_rx);
        uvm_config_db #(virtual iMfbTx #(2, 1, 8, 32, 3+32+128))::set(null, "uvm_test_top.m_env.m_mfb_tx_agent_mi", "vif", mi_mfb_tx);

        run_test();
    end

    ////////////////////////////
    // Instance DUT
    DUT DUT_U(
        .CLK   (CLK),
        .RESET (RESET),

        .pce_avalon_tx (pce_avalon_tx),
        .pce_avalon_rx (pce_avalon_rx),
        .ptc_mfb_rx    (ptc_mfb_rx),
        .ptc_mfb_tx    (ptc_mfb_tx),
        .mi_mfb_rx     (mi_mfb_rx),
        .mi_mfb_tx     (mi_mfb_tx)
   );
endmodule
