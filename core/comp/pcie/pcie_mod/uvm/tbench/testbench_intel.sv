// tbench_intel.sv: test bench for intel pcie
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:   Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;


// verilog_lint: waive module-filename
module testbench;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    localparam HDR_WIDTH       = 128;
    localparam PREFIX_WIDTH    = 32;
    localparam BAR_RANGE_WIDTH = 3;
    localparam AVST_UP_META_W   = HDR_WIDTH + PREFIX_WIDTH + 1;
    localparam AVST_DOWN_META_W = HDR_WIDTH + PREFIX_WIDTH + BAR_RANGE_WIDTH;

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

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if  pcie_user_reset[PCIE_ENDPOINTS](PCIE_USER_CLK);
    reset_if  pcie_sysrst_n[PCIE_CONS](PCIE_SYSCLK_N);
    reset_if  mi_reset(MI_CLK);
    reset_if  dma_reset(DMA_CLK);
    // For Intel (AVALON)
    avst_if #(
        .REGIONS(CQ_MFB_REGIONS),
        .REGION_SIZE(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE),
        .ITEM_WIDTH(ITEM_WIDTH),
        .META_WIDTH(AVST_DOWN_META_W)
    ) avst_down[PCIE_ENDPOINTS](PCIE_USER_CLK);
    avst_if #(
        .REGIONS(CC_MFB_REGIONS),
        .REGION_SIZE(CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE),
        .ITEM_WIDTH(ITEM_WIDTH),
        .META_WIDTH(AVST_UP_META_W)
    ) avst_up[PCIE_ENDPOINTS](PCIE_USER_CLK);
    // For Intel and Xilinx (MFB)
    mfb_if #(
        .REGIONS(RQ_MFB_REGIONS),
        .REGION_SIZE(RQ_MFB_REGION_SIZE),
        .BLOCK_SIZE(RQ_MFB_BLOCK_SIZE),
        .ITEM_WIDTH(ITEM_WIDTH),
        .META_WIDTH(/*sv_pcie_meta_pack::PCIE_RQ_META_WIDTH*/ 0)
    ) dma_rq_mfb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mvb_if #(
        .ITEMS(RQ_MFB_REGIONS),
        .ITEM_WIDTH(sv_dma_bus_pack::DMA_UPHDR_WIDTH)
    ) dma_rq_mvb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mfb_if #(
        .REGIONS(RC_MFB_REGIONS),
        .REGION_SIZE(RC_MFB_REGION_SIZE),
        .BLOCK_SIZE(RC_MFB_BLOCK_SIZE),
        .ITEM_WIDTH(ITEM_WIDTH),
        .META_WIDTH(/*sv_pcie_meta_pack::PCIE_RC_META_WIDTH*/ 0)
    ) dma_rc_mfb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mvb_if #(
        .ITEMS(RC_MFB_REGIONS),
        .ITEM_WIDTH(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)
    ) dma_rc_mvb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);

    mfb_if #(
        .REGIONS(CQ_MFB_REGIONS),
        .REGION_SIZE(CQ_MFB_REGION_SIZE),
        .BLOCK_SIZE(CQ_MFB_BLOCK_SIZE),
        .ITEM_WIDTH(ITEM_WIDTH),
        .META_WIDTH(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)
    ) dma_cq_mfb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mfb_if #(
        .REGIONS(CC_MFB_REGIONS),
        .REGION_SIZE(CC_MFB_REGION_SIZE),
        .BLOCK_SIZE(CC_MFB_BLOCK_SIZE),
        .ITEM_WIDTH(ITEM_WIDTH),
        .META_WIDTH(sv_pcie_meta_pack::PCIE_CC_META_WIDTH)
    ) dma_cc_mfb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mi_if #(
        .DATA_WIDTH(32),
        .ADDR_WIDTH(32)
    ) config_mi[PCIE_ENDPOINTS](MI_CLK);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always #(PCIE_SYSCLK_CLK_PERIOD) PCIE_SYSCLK_P = ~PCIE_SYSCLK_P;
    always #(PCIE_SYSCLK_CLK_PERIOD) PCIE_SYSCLK_N = ~PCIE_SYSCLK_N;
    always #(DMA_CLK_PERIOD) PCIE_USER_CLK         = ~PCIE_USER_CLK;
    always #(DMA_CLK_PERIOD) DMA_CLK               = ~DMA_CLK;
    always #(MI_CLK_PERIOD) MI_CLK                 = ~MI_CLK;


    //BUGFIX QUESTASIM
    generate
        if (PCIE_ENDPOINTS == 1) begin : gen_PCIE_ENDPOINTS_1
            bind PCIE_TRANSACTION_CTRL : $root.testbench.DUT_U.VHDL_DUT_U.pcie_ctrl_g[0].pcie_ctrl_i.ptc_g.ptc_i probe_inf #(MVB_UP_ITEMS*(1 + PCIE_TAG_WIDTH + sv_dma_bus_pack::DMA_UPHDR_WIDTH)) probe_tag(
                                .event_signal({tagm_mvb_out_src_rdy & tagm_mvb_out_dst_rdy}),
                                .event_data  ({tagm_mvb_out, tagm_mvb_out_tag, tagm_mvb_out_vld}),
                                .CLK         (CLK));
        end else if (PCIE_ENDPOINTS == 2) begin : gen_PCIE_ENDPOINTS_2
            bind PCIE_TRANSACTION_CTRL : $root.testbench.DUT_U.VHDL_DUT_U.pcie_ctrl_g[0].pcie_ctrl_i.ptc_g.ptc_i probe_inf #(MVB_UP_ITEMS*(1 + PCIE_TAG_WIDTH + sv_dma_bus_pack::DMA_UPHDR_WIDTH)) probe_tag(
                                .event_signal({tagm_mvb_out_src_rdy & tagm_mvb_out_dst_rdy}),
                                .event_data  ({tagm_mvb_out, tagm_mvb_out_tag, tagm_mvb_out_vld}),
                                .CLK         (CLK));
            bind PCIE_TRANSACTION_CTRL : $root.testbench.DUT_U.VHDL_DUT_U.pcie_ctrl_g[1].pcie_ctrl_i.ptc_g.ptc_i probe_inf #(MVB_UP_ITEMS*(1 + PCIE_TAG_WIDTH + sv_dma_bus_pack::DMA_UPHDR_WIDTH)) probe_tag(
                                .event_signal({tagm_mvb_out_src_rdy & tagm_mvb_out_dst_rdy}),
                                .event_data  ({tagm_mvb_out, tagm_mvb_out_tag, tagm_mvb_out_vld}),
                                .CLK         (CLK));
        end else if (PCIE_ENDPOINTS == 4) begin : gen_PCIE_ENDPOINTS_4
            bind PCIE_TRANSACTION_CTRL : $root.testbench.DUT_U.VHDL_DUT_U.pcie_ctrl_g[0].pcie_ctrl_i.ptc_g.ptc_i probe_inf #(MVB_UP_ITEMS*(1 + PCIE_TAG_WIDTH + sv_dma_bus_pack::DMA_UPHDR_WIDTH)) probe_tag(
                                .event_signal({tagm_mvb_out_src_rdy & tagm_mvb_out_dst_rdy}),
                                .event_data  ({tagm_mvb_out, tagm_mvb_out_tag, tagm_mvb_out_vld}),
                                .CLK         (CLK));
            bind PCIE_TRANSACTION_CTRL : $root.testbench.DUT_U.VHDL_DUT_U.pcie_ctrl_g[1].pcie_ctrl_i.ptc_g.ptc_i probe_inf #(MVB_UP_ITEMS*(1 + PCIE_TAG_WIDTH + sv_dma_bus_pack::DMA_UPHDR_WIDTH)) probe_tag(
                                .event_signal({tagm_mvb_out_src_rdy & tagm_mvb_out_dst_rdy}),
                                .event_data  ({tagm_mvb_out, tagm_mvb_out_tag, tagm_mvb_out_vld}),
                                .CLK         (CLK));
            bind PCIE_TRANSACTION_CTRL : $root.testbench.DUT_U.VHDL_DUT_U.pcie_ctrl_g[2].pcie_ctrl_i.ptc_g.ptc_i probe_inf #(MVB_UP_ITEMS*(1 + PCIE_TAG_WIDTH + sv_dma_bus_pack::DMA_UPHDR_WIDTH)) probe_tag(
                                .event_signal({tagm_mvb_out_src_rdy & tagm_mvb_out_dst_rdy}),
                                .event_data  ({tagm_mvb_out, tagm_mvb_out_tag, tagm_mvb_out_vld}),
                                .CLK         (CLK));
            bind PCIE_TRANSACTION_CTRL : $root.testbench.DUT_U.VHDL_DUT_U.pcie_ctrl_g[3].pcie_ctrl_i.ptc_g.ptc_i probe_inf #(MVB_UP_ITEMS*(1 + PCIE_TAG_WIDTH + sv_dma_bus_pack::DMA_UPHDR_WIDTH)) probe_tag(
                                .event_signal({tagm_mvb_out_src_rdy & tagm_mvb_out_dst_rdy}),
                                .event_data  ({tagm_mvb_out, tagm_mvb_out_tag, tagm_mvb_out_vld}),
                                .CLK         (CLK));
        end else begin : gen_PCIE_ENDPOINTS_unsupported
            $error("\nERROR: Unsupported combination (due to bug in questasim. Questasim cannot operate with array path in bind)\n");
        end
    endgenerate

    for (genvar pcie_e = 0; pcie_e < PCIE_ENDPOINTS; pcie_e++) begin : gen_pcie_endpoints
        //bind PCIE_TRANSACTION_CTRL : DUT_U.VHDL_DUT_U.pcie_ctrl_g[pcie_e].pcie_ctrl_i.ptc_g.ptc_i probe_inf #(MVB_UP_ITEMS*(1 + PCIE_TAG_WIDTH + sv_dma_bus_pack::DMA_UPHDR_WIDTH)) probe_tag(
        //                    .event_signal({tagm_mvb_out_src_rdy & tagm_mvb_out_dst_rdy}),
        //                    .event_data  ({tagm_mvb_out, tagm_mvb_out_tag, tagm_mvb_out_vld}),
        //                    .CLK         (CLK));


        assign pcie_user_reset[pcie_e].RESET = pcie_user_reset_logic[pcie_e];
    end

    for (genvar pcie_clks = 0; pcie_clks < PCIE_CONS*PCIE_CLKS; pcie_clks++) begin : gen_pcie_clks
        assign pcie_sysclk_p_logic[pcie_clks] = PCIE_SYSCLK_P;
        assign pcie_sysclk_n_logic[pcie_clks] = PCIE_SYSCLK_N;
    end
    for (genvar pcie_c = 0; pcie_c < PCIE_CONS; pcie_c++) begin : gen_pcie_cons
        assign pcie_sysrst_n_logic[pcie_c] = pcie_sysrst_n[pcie_c].RESET;
        // assign INIT_DONE_N = !pcie_sysrst_n[pcie_c].RESET;
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;

        // AVALON interface
        automatic virtual avst_if #(
            .REGIONS(CQ_MFB_REGIONS),
            .REGION_SIZE(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE),
            .ITEM_WIDTH(ITEM_WIDTH),
            .META_WIDTH(AVST_DOWN_META_W)
        ) v_avst_down[PCIE_ENDPOINTS] = avst_down;
        automatic virtual avst_if #(
            .REGIONS(CC_MFB_REGIONS),
            .REGION_SIZE(CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE),
            .ITEM_WIDTH(ITEM_WIDTH),
            .META_WIDTH(AVST_UP_META_W)
        ) v_avst_up[PCIE_ENDPOINTS] = avst_up;

        // DMA
        automatic virtual mfb_if #(
            .REGIONS(RQ_MFB_REGIONS),
            .REGION_SIZE(RQ_MFB_REGION_SIZE),
            .BLOCK_SIZE(RQ_MFB_BLOCK_SIZE),
            .ITEM_WIDTH(ITEM_WIDTH),
            .META_WIDTH(0)
        ) v_rq_mfb[PCIE_ENDPOINTS][DMA_PORTS] = dma_rq_mfb;
        automatic virtual mvb_if #(
            .ITEMS(RQ_MFB_REGIONS),
            .ITEM_WIDTH(sv_dma_bus_pack::DMA_UPHDR_WIDTH)
        ) v_rq_mvb[PCIE_ENDPOINTS][DMA_PORTS] = dma_rq_mvb;
        automatic virtual mfb_if #(
            .REGIONS(RC_MFB_REGIONS),
            .REGION_SIZE(RC_MFB_REGION_SIZE),
            .BLOCK_SIZE(RC_MFB_BLOCK_SIZE),
            .ITEM_WIDTH(ITEM_WIDTH),
            .META_WIDTH(0)
        ) v_rc_mfb[PCIE_ENDPOINTS][DMA_PORTS] = dma_rc_mfb;
        automatic virtual mvb_if #(
            .ITEMS(RC_MFB_REGIONS),
            .ITEM_WIDTH(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)
        ) v_rc_mvb[PCIE_ENDPOINTS][DMA_PORTS] = dma_rc_mvb;

        automatic virtual mfb_if #(
            .REGIONS(CQ_MFB_REGIONS),
            .REGION_SIZE(CQ_MFB_REGION_SIZE),
            .BLOCK_SIZE(CQ_MFB_BLOCK_SIZE),
            .ITEM_WIDTH(ITEM_WIDTH),
            .META_WIDTH(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)
        ) v_cq_mfb[PCIE_ENDPOINTS][DMA_PORTS] = dma_cq_mfb;
        automatic virtual mfb_if #(
            .REGIONS(CC_MFB_REGIONS),
            .REGION_SIZE(CC_MFB_REGION_SIZE),
            .BLOCK_SIZE(CC_MFB_BLOCK_SIZE),
            .ITEM_WIDTH(ITEM_WIDTH),
            .META_WIDTH(sv_pcie_meta_pack::PCIE_CC_META_WIDTH)
        ) v_cc_mfb[PCIE_ENDPOINTS][DMA_PORTS] = dma_cc_mfb;

        automatic virtual mi_if #(
            .DATA_WIDTH(32),
            .ADDR_WIDTH(32)
        ) v_mi_config[PCIE_ENDPOINTS] = config_mi;
        automatic virtual reset_if v_pcie_user_reset[PCIE_ENDPOINTS] = pcie_user_reset;
        automatic virtual reset_if v_pcie_sysrst_n[PCIE_CONS]        = pcie_sysrst_n;


        for (int unsigned pcie_con = 0; pcie_con < PCIE_CONS; pcie_con++) begin
            uvm_config_db#(virtual reset_if)::set(null, "", $sformatf("vif_pcie_sysrst_n_%0d", pcie_con), v_pcie_sysrst_n[pcie_con]);
        end

        for (int unsigned pcie_e = 0; pcie_e < PCIE_ENDPOINTS; pcie_e++) begin
            string i_string;
            i_string.itoa(pcie_e);
            uvm_config_db#(virtual mi_if #(
                .DATA_WIDTH(32),
                .ADDR_WIDTH(32)
            ))::set(null, "", {"vif_mi_",i_string}, v_mi_config[pcie_e]);
            uvm_config_db#(virtual reset_if)::set(null, "", {"vif_pcie_user_reset_",i_string}, v_pcie_user_reset[pcie_e]);
            uvm_config_db#(virtual avst_if #(
                .REGIONS(CQ_MFB_REGIONS),
                .REGION_SIZE(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE),
                .ITEM_WIDTH(ITEM_WIDTH),
                .META_WIDTH(AVST_DOWN_META_W)
            ))::set(null, "", {"vif_pcie_", i_string, "_down_avst"}, v_avst_down[pcie_e]);
            uvm_config_db#(virtual avst_if #(
                .REGIONS(CC_MFB_REGIONS),
                .REGION_SIZE(CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE),
                .ITEM_WIDTH(ITEM_WIDTH),
                .META_WIDTH(AVST_UP_META_W)
            ))::set(null, "", {"vif_pcie_", i_string, "_up_avst"}, v_avst_up[pcie_e]);

            for (int dma = 0; dma < DMA_PORTS; dma++) begin
                string dma_string;
                dma_string = $sformatf("%0d_%0d", pcie_e, dma);
                uvm_config_db#(virtual mfb_if #(
                    .REGIONS(RQ_MFB_REGIONS),
                    .REGION_SIZE(RQ_MFB_REGION_SIZE),
                    .BLOCK_SIZE(RQ_MFB_BLOCK_SIZE),
                    .ITEM_WIDTH(ITEM_WIDTH),
                    .META_WIDTH(0)
                ))::set(null, "", {"vif_dma_",dma_string, "_rq_mfb"}, v_rq_mfb[pcie_e][dma]);
                uvm_config_db#(virtual mvb_if #(
                    .ITEMS(RQ_MFB_REGIONS),
                    .ITEM_WIDTH(sv_dma_bus_pack::DMA_UPHDR_WIDTH)
                ))::set(null, "", {"vif_dma_", dma_string, "_rq_mvb"}, v_rq_mvb[pcie_e][dma]);
                uvm_config_db#(virtual mfb_if #(
                    .REGIONS(RC_MFB_REGIONS),
                    .REGION_SIZE(RC_MFB_REGION_SIZE),
                    .BLOCK_SIZE(RC_MFB_BLOCK_SIZE),
                    .ITEM_WIDTH(ITEM_WIDTH),
                    .META_WIDTH(0)
                ))::set(null, "", {"vif_dma_",dma_string, "_rc_mfb"}, v_rc_mfb[pcie_e][dma]);
                uvm_config_db#(virtual mvb_if #(
                    .ITEMS(RC_MFB_REGIONS),
                    .ITEM_WIDTH(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)
                ))::set(null, "", {"vif_dma_",dma_string, "_rc_mvb"}, v_rc_mvb[pcie_e][dma]);

                uvm_config_db#(virtual mfb_if #(
                    .REGIONS(CQ_MFB_REGIONS),
                    .REGION_SIZE(CQ_MFB_REGION_SIZE),
                    .BLOCK_SIZE(CQ_MFB_BLOCK_SIZE),
                    .ITEM_WIDTH(ITEM_WIDTH),
                    .META_WIDTH(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)
                ))::set(null, "", {"vif_dma_cq_",dma_string, "_mfb"}, v_cq_mfb[pcie_e][dma]);
                uvm_config_db#(virtual mfb_if #(
                    .REGIONS(CC_MFB_REGIONS),
                    .REGION_SIZE(CC_MFB_REGION_SIZE),
                    .BLOCK_SIZE(CC_MFB_BLOCK_SIZE),
                    .ITEM_WIDTH(ITEM_WIDTH),
                    .META_WIDTH(sv_pcie_meta_pack::PCIE_CC_META_WIDTH)
                ))::set(null, "", {"vif_dma_cc_",dma_string, "_mfb"}, v_cc_mfb[pcie_e][dma]);
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
        uvm_pcie::root::type_id::set_inst_override(
            uvm_pcie_avst::root#(
                .REGIONS(CQ_MFB_REGIONS),
                .REGIONS_SIZE(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE),
                .RDY_LATENCY(27),
                .STRADDLING(STRADDLING)
            )::get_type(),
            "uvm_test_top.*"
        );

        run_test();
        $stop(2);
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // DUT
    dut DUT_U (
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
        // physical endpoints
        for (genvar pcie_connection = 0; pcie_connection < PCIE_CONS; pcie_connection++) begin : gen_pcie_cons_greybox
            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_hip_clk[pcie_connection] = PCIE_USER_CLK;
        end

        // logical endpoints (bifurcation)
        for (genvar pcie_e = 0; pcie_e < PCIE_ENDPOINTS; pcie_e++) begin : pcie_endpoins_gen
            logic [CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*ITEM_WIDTH-1 : 0]        avst_down_data ;
            logic [CQ_MFB_REGIONS*$clog2(RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE)          -1 : 0] avst_down_empty;
            logic [CQ_MFB_REGIONS*HDR_WIDTH      -1 : 0]                                        down_hdr      ;
            logic [CQ_MFB_REGIONS*PREFIX_WIDTH   -1 : 0]                                        down_prefix   ;
            logic [CQ_MFB_REGIONS*BAR_RANGE_WIDTH-1 : 0]                                        down_bar_range;

            logic [CC_MFB_REGIONS*HDR_WIDTH   -1 : 0] up_hdr   ;
            logic [CC_MFB_REGIONS*PREFIX_WIDTH-1 : 0] up_prefix;
            logic [CC_MFB_REGIONS             -1 : 0] up_error ;


            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_link_up_comb[pcie_e]  = '1;

            for (genvar reg_it = 0; reg_it < CQ_MFB_REGIONS; reg_it++) begin : avst_down_gen
                localparam CQ_REGION_SIZE = CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE;

                assign avst_down_data[(reg_it+1)*CQ_REGION_SIZE*ITEM_WIDTH-1 -: CQ_REGION_SIZE*ITEM_WIDTH] = avst_down[pcie_e].DATA[reg_it];
                assign {
                    down_bar_range[(reg_it+1)*BAR_RANGE_WIDTH-1 -: BAR_RANGE_WIDTH],
                    down_prefix   [(reg_it+1)*PREFIX_WIDTH   -1 -: PREFIX_WIDTH],
                    down_hdr      [(reg_it+1)*HDR_WIDTH      -1 -: HDR_WIDTH]
                } = avst_down[pcie_e].META[reg_it];

                assign avst_down_empty[(reg_it+1)*$clog2(CQ_REGION_SIZE)-1 -: $clog2(CQ_REGION_SIZE)] = avst_down[pcie_e].EMPTY[reg_it];
                //QUESTA BUG: when (CQ_MFB_REGION_SIZE == 0) then simple assigment fail
                assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_DOWN_SOP[reg_it]    = avst_down[pcie_e].SOP[reg_it];
                assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_DOWN_EOP[reg_it]    = avst_down[pcie_e].EOP[reg_it];
                assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_DOWN_VALID[reg_it]  = avst_down[pcie_e].VALID[reg_it];
            end

            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_DOWN_EMPTY     = avst_down_empty;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_DOWN_BAR_RANGE = down_bar_range;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_DOWN_PREFIX    = down_prefix;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_DOWN_HDR       = down_hdr;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_DOWN_DATA   = avst_down_data;
            //assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_DOWN_SOP    = avst_down[pcie_e].SOP;
            //assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_DOWN_EOP    = avst_down[pcie_e].EOP;
            //assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_DOWN_VALID  = avst_down[pcie_e].VALID;
            assign avst_down[pcie_e].READY = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_DOWN_READY;


            for (genvar reg_it = 0; reg_it < CC_MFB_REGIONS; reg_it++) begin : gen_CC_MFB_REGIONS
                localparam CC_REGION_SIZE = CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE;
                assign avst_up[pcie_e].DATA[reg_it]  = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_UP_DATA[(reg_it+1)*CC_REGION_SIZE*ITEM_WIDTH-1 -: CC_REGION_SIZE*ITEM_WIDTH];
                assign avst_up[pcie_e].EMPTY[reg_it] = '0;

                assign avst_up[pcie_e].META[reg_it] = {
                    up_error [(reg_it+1)*1              -1 -: 1],
                    up_prefix[(reg_it+1)*PREFIX_WIDTH   -1 -: PREFIX_WIDTH],
                    up_hdr   [(reg_it+1)*HDR_WIDTH      -1 -: HDR_WIDTH]
                };
            end
            assign avst_up[pcie_e].SOP   = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_UP_SOP;
            assign avst_up[pcie_e].EOP   = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_UP_EOP;
            assign avst_up[pcie_e].VALID = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_UP_VALID;
            assign up_hdr        = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_UP_HDR;
            assign up_prefix     = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_UP_PREFIX;
            assign up_error      = DUT_U.VHDL_DUT_U.pcie_core_i.pcie_adapter_g[pcie_e].pcie_adapter_i.AVST_UP_ERROR;
            assign DUT_U.VHDL_DUT_U.pcie_core_i.pcie_avst_up_ready[pcie_e] = avst_up[pcie_e].READY;

        end

    endgenerate
endmodule
