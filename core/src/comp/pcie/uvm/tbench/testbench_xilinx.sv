// tbench_xilinx.sv: Testbench for xilinx pcie
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:   Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    localparam HDR_WIDTH       = 128;
    localparam PREFIX_WIDTH    = 32;
    localparam BAR_RANGE_WIDTH = 3;
    localparam IS_INTEL_DEV    = (DEVICE == "STRATIX10" || DEVICE == "AGILEX");

    localparam CQ_DATA_WIDTH  = CQ_MFB_REGIONS * CQ_MFB_REGION_SIZE * CQ_MFB_BLOCK_SIZE*ITEM_WIDTH;
    localparam CC_DATA_WIDTH  = CC_MFB_REGIONS * CC_MFB_REGION_SIZE * CC_MFB_BLOCK_SIZE*ITEM_WIDTH;
    localparam RQ_DATA_WIDTH  = RQ_MFB_REGIONS * RQ_MFB_REGION_SIZE * RQ_MFB_BLOCK_SIZE*ITEM_WIDTH;
    localparam RC_DATA_WIDTH  = RC_MFB_REGIONS * RC_MFB_REGION_SIZE * RC_MFB_BLOCK_SIZE*ITEM_WIDTH;


    // Signals
    logic PCIE_SYSCLK_P = '0;
    logic PCIE_SYSCLK_N = '0;
    logic PCIE_USER_CLK = '0;
    logic [PCIE_CONS*PCIE_CLKS-1 : 0] pcie_sysclk_p_logic;
    logic [PCIE_CONS*PCIE_CLKS-1 : 0] pcie_sysclk_n_logic;
    logic [PCIE_ENDPOINTS-1 : 0]      pcie_user_clk_logic;
    logic [PCIE_ENDPOINTS-1 : 0]      pcie_user_reset_logic;
    logic [PCIE_CONS-1 : 0]           pcie_sysrst_n_logic;
    logic INIT_DONE_N = 1;
    logic DMA_CLK = 0;
    logic MI_CLK = 0;

    logic [CQ_MFB_REGIONS*HDR_WIDTH      -1 : 0] down_hdr[PCIE_CONS]      ;
    logic [CQ_MFB_REGIONS*PREFIX_WIDTH   -1 : 0] down_prefix[PCIE_CONS]   ;
    logic [CQ_MFB_REGIONS*BAR_RANGE_WIDTH-1 : 0] down_bar_range[PCIE_CONS];

    logic [PCIE_ENDPOINTS*CC_MFB_REGIONS*HDR_WIDTH                                                                 -1: 0] up_hdr[PCIE_CONS];
    logic [PCIE_ENDPOINTS*CC_MFB_REGIONS*PREFIX_WIDTH                                                              -1: 0] up_prefix[PCIE_CONS];
    logic [PCIE_ENDPOINTS*CC_MFB_REGIONS                                                                           -1: 0] up_error[PCIE_CONS];

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if  pcie_user_reset[PCIE_ENDPOINTS](PCIE_USER_CLK);
    reset_if  pcie_sysrst_n[PCIE_CONS](PCIE_SYSCLK_N);
    reset_if  mi_reset(MI_CLK);
    reset_if  dma_reset(DMA_CLK);
    // For Xilinx (AXI)
    axi_if #(CQ_DATA_WIDTH, AXI_CQUSER_WIDTH) cq_axi[PCIE_ENDPOINTS](PCIE_USER_CLK);
    axi_if #(CC_DATA_WIDTH, AXI_CCUSER_WIDTH) cc_axi[PCIE_ENDPOINTS](PCIE_USER_CLK);
    axi_if #(RQ_DATA_WIDTH, AXI_RQUSER_WIDTH) rq_axi[PCIE_ENDPOINTS](PCIE_USER_CLK);
    axi_if #(RC_DATA_WIDTH, AXI_RCUSER_WIDTH) rc_axi[PCIE_ENDPOINTS](PCIE_USER_CLK);
    // For Intel and Xilinx (MFB)
    mfb_if #(RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, ITEM_WIDTH, RQ_MFB_META_W)  dma_rq_mfb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mvb_if #(RQ_MFB_REGIONS, sv_dma_bus_pack::DMA_UPHDR_WIDTH)                                  dma_rq_mvb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mfb_if #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, ITEM_WIDTH, RC_MFB_META_W)  dma_rc_mfb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mvb_if #(RC_MFB_REGIONS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)                                dma_rc_mvb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);

    mfb_if #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, CQ_MFB_META_W)  dma_cq_mfb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mfb_if #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, ITEM_WIDTH, CC_MFB_META_W)  dma_cc_mfb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mi_if  #(32, 32) config_mi[PCIE_ENDPOINTS] (MI_CLK);

    //bind TAG_PROBE : DUT_U.VHDL_DUT_U. pcie_ctrl_g[it].pcie_ctrl_i.ptc_i  probe_inf #(2*REGIONS) probe_drop({tagm_mvb_out_src_rdy & tagm_mvb_out_src_rdy},
    //                                                                                                        {s_rx_eof_orig_reg, s_rx_force_drop_reg}, PCIE_USER_CLK);
    generate
        if (PCIE_ENDPOINTS == 1) begin
            bind PCIE_TRANSACTION_CTRL : DUT_U.VHDL_DUT_U.pcie_ctrl_g[0].pcie_ctrl_i.ptc_g.ptc_i probe_inf #(MVB_UP_ITEMS*(1 + PCIE_TAG_WIDTH + sv_dma_bus_pack::DMA_UPHDR_WIDTH)) probe_tag(
                            {tagm_mvb_out_src_rdy & tagm_mvb_out_dst_rdy}, {tagm_mvb_out, tagm_mvb_out_tag, tagm_mvb_out_vld}, CLK);
        end else begin
            $error("\nERROR: Unsupported combination (due to bug in questasim. Questasim cannot operate with array path in bind)\n");
        end
    endgenerate

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(PCIE_SYSCLK_CLK_PERIOD) PCIE_SYSCLK_P = ~PCIE_SYSCLK_P;
    always #(PCIE_SYSCLK_CLK_PERIOD) PCIE_SYSCLK_N = ~PCIE_SYSCLK_N;
    always #(DMA_CLK_PERIOD) PCIE_USER_CLK         = ~PCIE_USER_CLK;
    always #(DMA_CLK_PERIOD) DMA_CLK               = ~DMA_CLK;
    always #(MI_CLK_PERIOD) MI_CLK                 = ~MI_CLK;

    for (genvar pcie_e = 0; pcie_e < PCIE_ENDPOINTS; pcie_e++) begin
        assign pcie_user_reset[pcie_e].RESET = pcie_user_reset_logic[pcie_e];
    end

    for (genvar pcie_clks = 0; pcie_clks < PCIE_CONS*PCIE_CLKS; pcie_clks++) begin
        assign pcie_sysclk_p_logic[pcie_clks] = PCIE_SYSCLK_P;
        assign pcie_sysclk_n_logic[pcie_clks] = PCIE_SYSCLK_N;
    end
    for (genvar pcie_c = 0; pcie_c < PCIE_CONS; pcie_c++) begin
        assign pcie_sysrst_n_logic[pcie_c] = pcie_sysrst_n[pcie_c].RESET;
        // assign INIT_DONE_N = !pcie_sysrst_n[pcie_c].RESET;
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;
        // DMA
        automatic virtual mfb_if #(RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, ITEM_WIDTH, RQ_MFB_META_W) v_rq_mfb[PCIE_ENDPOINTS][DMA_PORTS] = dma_rq_mfb;
        automatic virtual mvb_if #(RQ_MFB_REGIONS, sv_dma_bus_pack::DMA_UPHDR_WIDTH)                                 v_rq_mvb[PCIE_ENDPOINTS][DMA_PORTS] = dma_rq_mvb;
        automatic virtual mfb_if #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, ITEM_WIDTH, RC_MFB_META_W) v_rc_mfb[PCIE_ENDPOINTS][DMA_PORTS] = dma_rc_mfb;
        automatic virtual mvb_if #(RC_MFB_REGIONS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)                               v_rc_mvb[PCIE_ENDPOINTS][DMA_PORTS] = dma_rc_mvb;

        automatic virtual mfb_if #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, CQ_MFB_META_W) v_cq_mfb[PCIE_ENDPOINTS][DMA_PORTS] = dma_cq_mfb;
        automatic virtual mfb_if #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, ITEM_WIDTH, CC_MFB_META_W) v_cc_mfb[PCIE_ENDPOINTS][DMA_PORTS] = dma_cc_mfb;

        // AXI
        automatic virtual axi_if #(CQ_DATA_WIDTH, AXI_CQUSER_WIDTH)                                                        v_cq_axi[PCIE_ENDPOINTS] = cq_axi;
        automatic virtual axi_if #(CC_DATA_WIDTH, AXI_CCUSER_WIDTH)                                                        v_cc_axi[PCIE_ENDPOINTS] = cc_axi;
        automatic virtual axi_if #(RQ_DATA_WIDTH, AXI_RQUSER_WIDTH)                                                        v_rq_axi[PCIE_ENDPOINTS] = rq_axi;
        automatic virtual axi_if #(RC_DATA_WIDTH, AXI_RCUSER_WIDTH)                                                        v_rc_axi[PCIE_ENDPOINTS] = rc_axi;

        automatic virtual mi_if #(32, 32)                                                                                   v_mi_config[PCIE_ENDPOINTS]       = config_mi;
        automatic virtual reset_if                                                                                          v_pcie_user_reset[PCIE_ENDPOINTS] = pcie_user_reset;
        automatic virtual reset_if                                                                                          v_pcie_sysrst_n[PCIE_CONS]        = pcie_sysrst_n;

        for (int unsigned pcie_e = 0; pcie_e < PCIE_ENDPOINTS; pcie_e++) begin
            string i_string;
            i_string.itoa(pcie_e);
            uvm_config_db#(virtual mi_if #(32, 32))::set(null, "", {"vif_mi_",i_string}, v_mi_config[pcie_e]);
            uvm_config_db#(virtual reset_if)::set(null, "", {"vif_pcie_user_reset_",i_string}, v_pcie_user_reset[pcie_e]);
            uvm_config_db#(virtual reset_if)::set(null, "", {"vif_pcie_sysrst_n_",i_string}, v_pcie_sysrst_n[pcie_e]);

            // AXI
            uvm_config_db#(virtual axi_if #(CQ_DATA_WIDTH, AXI_CQUSER_WIDTH))::set(null, "", {"vif_pcie_", i_string, "_cq"}, v_cq_axi[pcie_e]);
            uvm_config_db#(virtual axi_if #(CC_DATA_WIDTH, AXI_CCUSER_WIDTH))::set(null, "", {"vif_pcie_", i_string, "_cc"}, v_cc_axi[pcie_e]);
            uvm_config_db#(virtual axi_if #(RQ_DATA_WIDTH, AXI_RQUSER_WIDTH))::set(null, "", {"vif_pcie_", i_string, "_rq"}, v_rq_axi[pcie_e]);
            uvm_config_db#(virtual axi_if #(RC_DATA_WIDTH, AXI_RCUSER_WIDTH))::set(null, "", {"vif_pcie_", i_string, "_rc"}, v_rc_axi[pcie_e]);

            for (int dma = 0; dma < DMA_PORTS; dma++) begin
                string dma_string;
                dma_string = $sformatf("%0d_%0d", pcie_e, dma);
                uvm_config_db#(virtual mfb_if #(RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, ITEM_WIDTH, RQ_MFB_META_W))::set(null, "", {"vif_rq_mfb_",dma_string}, v_rq_mfb[pcie_e][dma]);
                uvm_config_db#(virtual mvb_if #(RQ_MFB_REGIONS, sv_dma_bus_pack::DMA_UPHDR_WIDTH))::set(null, "", {"vif_rq_mvb_",dma_string}, v_rq_mvb[pcie_e][dma]);
                uvm_config_db#(virtual mfb_if #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, ITEM_WIDTH, RC_MFB_META_W))::set(null, "", {"vif_rc_mfb_",dma_string}, v_rc_mfb[pcie_e][dma]);
                uvm_config_db#(virtual mvb_if #(RC_MFB_REGIONS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH))::set(null, "", {"vif_rc_mvb_",dma_string}, v_rc_mvb[pcie_e][dma]);

                uvm_config_db#(virtual mfb_if #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, CQ_MFB_META_W))::set(null, "", {"vif_cq_mfb_",dma_string}, v_cq_mfb[pcie_e][dma]);
                uvm_config_db#(virtual mfb_if #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, ITEM_WIDTH, CC_MFB_META_W))::set(null, "", {"vif_cc_mfb_",dma_string}, v_cc_mfb[pcie_e][dma]);
            end
        end

        uvm_config_db#(virtual reset_if)::set(null, "", "vif_dma_reset", dma_reset);
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_mi_reset", mi_reset);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        //REWRITE PCIE
        uvm_pcie::env::type_id::set_inst_override(
            uvm_pcie_xilinx::env#(
                CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, AXI_CQUSER_WIDTH,
                CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, AXI_CCUSER_WIDTH,
                RQ_MFB_REGIONS, RQ_MFB_REGION_SIZE, RQ_MFB_BLOCK_SIZE, AXI_RQUSER_WIDTH,
                RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, AXI_RCUSER_WIDTH,
                AXI_STRADDLING)::get_type(), "uvm_test_top.*" );

        run_test();
        $stop(2);
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // DUT
    DUT DUT_U (
        .PCIE_SYSCLK_P   (pcie_sysclk_p_logic),
        .PCIE_SYSCLK_N   (pcie_sysclk_n_logic),
        .PCIE_USER_CLK   (pcie_user_clk_logic),
        .PCIE_USER_RESET (pcie_user_reset_logic),
        .PCIE_SYSRST_N   (pcie_sysrst_n_logic),
        .INIT_DONE_N     (INIT_DONE_N),
        .DMA_CLK         (DMA_CLK),
        .DMA_RESET       (dma_reset.RESET),
        .MI_CLK          (MI_CLK),
        .MI_RESET        (mi_reset.RESET),
        .dma_rq_mfb      (dma_rq_mfb),
        .dma_rq_mvb      (dma_rq_mvb),
        .dma_rc_mfb      (dma_rc_mfb),
        .dma_rc_mvb      (dma_rc_mvb),
        .dma_cq_mfb      (dma_cq_mfb),
        .dma_cc_mfb      (dma_cc_mfb),
        .config_mi       (config_mi)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // GRAY BOX CONNECTION
    generate
        for (genvar pcie_e = 0; pcie_e < PCIE_ENDPOINTS; pcie_e++) begin

            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_hip_clk[pcie_e] = PCIE_USER_CLK;

            assign DUT_U.VHDL_DUT_U.pcie_core_i.cfg_phy_link_status[pcie_e][0]  = 1'b1;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.cfg_phy_link_status[pcie_e][1]  = 1'b1;

            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.CQ_AXI_DATA  = cq_axi[pcie_e].TDATA;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.CQ_AXI_USER  = cq_axi[pcie_e].TUSER;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.CQ_AXI_LAST  = cq_axi[pcie_e].TLAST;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.CQ_AXI_KEEP  = cq_axi[pcie_e].TKEEP;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.CQ_AXI_VALID = cq_axi[pcie_e].TVALID;
            assign cq_axi[pcie_e].TREADY = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.CQ_AXI_READY;

            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.RC_AXI_DATA  = rc_axi[pcie_e].TDATA;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.RC_AXI_USER  = rc_axi[pcie_e].TUSER;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.RC_AXI_LAST  = rc_axi[pcie_e].TLAST;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.RC_AXI_KEEP  = rc_axi[pcie_e].TKEEP;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.RC_AXI_VALID = rc_axi[pcie_e].TVALID;
            assign rc_axi[pcie_e].TREADY = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.RC_AXI_READY;

            assign cc_axi[pcie_e].TDATA  = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.CC_AXI_DATA;
            assign cc_axi[pcie_e].TUSER  = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.CC_AXI_USER;
            assign cc_axi[pcie_e].TLAST  = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.CC_AXI_LAST;
            assign cc_axi[pcie_e].TKEEP  = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.CC_AXI_KEEP;
            assign cc_axi[pcie_e].TVALID = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.CC_AXI_VALID;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.s_axis_cc_tready[pcie_e][0] = cc_axi[pcie_e].TREADY;

            assign rq_axi[pcie_e].TDATA  = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.RQ_AXI_DATA;
            assign rq_axi[pcie_e].TUSER  = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.RQ_AXI_USER;
            assign rq_axi[pcie_e].TLAST  = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.RQ_AXI_LAST;
            assign rq_axi[pcie_e].TKEEP  = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.RQ_AXI_KEEP;
            assign rq_axi[pcie_e].TVALID = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.RQ_AXI_VALID;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.s_axis_rq_tready[pcie_e][0] = rq_axi[pcie_e].TREADY;

            assign DUT_U.VHDL_DUT_U.pcie_core_i.cfg_rcb_status[pcie_e][0] = 1'b0;
        end
        
    endgenerate

endmodule
