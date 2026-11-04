// testbench_xilinx_versal.sv: Testbench for the Xilinx Versal PCIe (CPM5)
// Copyright (C) DynaNIC Semiconductors, Ltd.
// Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026

// SPDX-License-Identifier: BSD-3-Clause

// The Versal PCIe IP core is a part of the CIPS outside of the PCIE module. The PCIE_CORE
// (architecture VERSAL) gets the AXI and the configuration signals of the IP core via
// the MISC_TOP2PCIE and MISC_PCIE2TOP ports. This testbench connects the AXI agents to
// these ports, so the whole PCIE_CORE (including the MISC packing) is verified.
// Gen3x16 uses the 512b AXI interfaces, Gen4x16 and Gen5x8x8 the 1024b ones.

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;


// verilog_lint: waive module-filename
module testbench;

    localparam ITEM_WIDTH      = 32;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // AXI interfaces of the PCIe IP core
    localparam int unsigned AXI_ITEMS        = CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE;
    localparam int unsigned AXI_DATA_WIDTH   = AXI_ITEMS*ITEM_WIDTH;
    localparam int unsigned AXI_CQUSER_WIDTH = uvm_pcie_axi::tuser_width_get(AXI_ITEMS, uvm_pcie_axi::AXI_CQ, DEVICE);
    localparam int unsigned AXI_CCUSER_WIDTH = uvm_pcie_axi::tuser_width_get(AXI_ITEMS, uvm_pcie_axi::AXI_CC, DEVICE);
    localparam int unsigned AXI_RQUSER_WIDTH = uvm_pcie_axi::tuser_width_get(AXI_ITEMS, uvm_pcie_axi::AXI_RQ, DEVICE);
    localparam int unsigned AXI_RCUSER_WIDTH = uvm_pcie_axi::tuser_width_get(AXI_ITEMS, uvm_pcie_axi::AXI_RC, DEVICE);

    // The MISC signals, the same order of the fields as in pcie_misc_versal_pkg.vhd (the first field is at the MSB)
    typedef struct packed {
        logic                          USER_CLK;
        logic                          USER_RESET;
        logic                          USER_LNK_UP;
        logic                          S_AXIS_RQ_TREADY;
        logic [AXI_DATA_WIDTH-1    :0] M_AXIS_RC_TDATA;
        logic [AXI_DATA_WIDTH/32-1 :0] M_AXIS_RC_TKEEP;
        logic                          M_AXIS_RC_TLAST;
        logic [AXI_RCUSER_WIDTH-1  :0] M_AXIS_RC_TUSER;
        logic                          M_AXIS_RC_TVALID;
        logic [AXI_DATA_WIDTH-1    :0] M_AXIS_CQ_TDATA;
        logic [AXI_DATA_WIDTH/32-1 :0] M_AXIS_CQ_TKEEP;
        logic                          M_AXIS_CQ_TLAST;
        logic [AXI_CQUSER_WIDTH-1  :0] M_AXIS_CQ_TUSER;
        logic                          M_AXIS_CQ_TVALID;
        logic                          S_AXIS_CC_TREADY;
        logic [9:0]                    CFG_STATUS_RQ_TAG0;
        logic [9:0]                    CFG_STATUS_RQ_TAG1;
        logic [9:0]                    CFG_STATUS_RQ_TAG2;
        logic [9:0]                    CFG_STATUS_RQ_TAG3;
        logic                          CFG_STATUS_RQ_TAG_VLD0;
        logic                          CFG_STATUS_RQ_TAG_VLD1;
        logic                          CFG_STATUS_RQ_TAG_VLD2;
        logic                          CFG_STATUS_RQ_TAG_VLD3;
        logic                          CFG_STATUS_PHY_LINK_DOWN;
        logic [1:0]                    CFG_STATUS_PHY_LINK_STATUS;
        logic [2:0]                    CFG_STATUS_NEGOTIATED_WIDTH;
        logic [2:0]                    CFG_STATUS_CURRENT_SPEED;
        logic [1:0]                    CFG_STATUS_MAX_PAYLOAD;
        logic [2:0]                    CFG_STATUS_MAX_READ_REQ;
        logic [3:0]                    CFG_STATUS_FUNCTION_STATUS;
        logic [2:0]                    CFG_STATUS_FUNCTION_POWER_STATE;
        logic [1:0]                    CFG_STATUS_LINK_POWER_STATE;
        logic                          CFG_STATUS_LOCAL_ERROR_VALID;
        logic [4:0]                    CFG_STATUS_LOCAL_ERROR_OUT;
        logic [5:0]                    CFG_STATUS_LTSSM_STATE;
        logic [1:0]                    CFG_STATUS_RX_PM_STATE;
        logic [1:0]                    CFG_STATUS_TX_PM_STATE;
        logic                          CFG_STATUS_RCB_STATUS;
        logic [7:0]                    CFG_FC_PH;
        logic [11:0]                   CFG_FC_PD;
        logic [7:0]                    CFG_FC_NPH;
        logic [11:0]                   CFG_FC_NPD;
        logic                          CFG_EXT_READ_RECEIVED;
        logic                          CFG_EXT_WRITE_RECEIVED;
        logic [9:0]                    CFG_EXT_REGISTER_NUMBER;
        logic [15:0]                   CFG_EXT_FUNCTION_NUMBER;
        logic [31:0]                   CFG_EXT_WRITE_DATA;
        logic [3:0]                    CFG_EXT_WRITE_BYTE_ENABLE;
    } misc_pcie_out_t;

    typedef struct packed {
        logic [AXI_DATA_WIDTH-1    :0] S_AXIS_RQ_TDATA;
        logic [AXI_DATA_WIDTH/32-1 :0] S_AXIS_RQ_TKEEP;
        logic                          S_AXIS_RQ_TLAST;
        logic [AXI_RQUSER_WIDTH-1  :0] S_AXIS_RQ_TUSER;
        logic                          S_AXIS_RQ_TVALID;
        logic                          M_AXIS_RC_TREADY;
        logic                          M_AXIS_CQ_TREADY;
        logic [AXI_DATA_WIDTH-1    :0] S_AXIS_CC_TDATA;
        logic [AXI_DATA_WIDTH/32-1 :0] S_AXIS_CC_TKEEP;
        logic                          S_AXIS_CC_TLAST;
        logic [AXI_CCUSER_WIDTH-1  :0] S_AXIS_CC_TUSER;
        logic                          S_AXIS_CC_TVALID;
        logic [31:0]                   CFG_EXT_READ_DATA;
        logic                          CFG_EXT_READ_DATA_VALID;
    } misc_pcie_in_t;

    localparam int unsigned MISC_TOP2PCIE_WIDTH = $bits(misc_pcie_out_t);
    localparam int unsigned MISC_PCIE2TOP_WIDTH = $bits(misc_pcie_in_t);

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
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

    // Nets: the fields and the endpoint slices are driven by separate continuous assignments
    wire misc_pcie_out_t                                   misc_out[PCIE_ENDPOINTS];
    wire misc_pcie_in_t                                    misc_in[PCIE_ENDPOINTS];
    wire [PCIE_ENDPOINTS*MISC_TOP2PCIE_WIDTH-1 : 0]        misc_top2pcie;
    wire [PCIE_ENDPOINTS*MISC_PCIE2TOP_WIDTH-1 : 0]        misc_pcie2top;

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Interfaces
    reset_if  pcie_user_reset[PCIE_ENDPOINTS](PCIE_USER_CLK);
    reset_if  pcie_sysrst_n[PCIE_CONS](PCIE_SYSCLK_N);
    reset_if  mi_reset(MI_CLK);
    reset_if  dma_reset(DMA_CLK);
    // For Xilinx (AXI)
    axi_if #(
        .ITEMS       (AXI_ITEMS),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .TUSER_WIDTH (AXI_CQUSER_WIDTH)
    ) cq_axi[PCIE_ENDPOINTS](PCIE_USER_CLK);
    axi_if #(
        .ITEMS       (AXI_ITEMS),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .TUSER_WIDTH (AXI_CCUSER_WIDTH)
    ) cc_axi[PCIE_ENDPOINTS](PCIE_USER_CLK);
    axi_if #(
        .ITEMS       (AXI_ITEMS),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .TUSER_WIDTH (AXI_RQUSER_WIDTH)
    ) rq_axi[PCIE_ENDPOINTS](PCIE_USER_CLK);
    axi_if #(
        .ITEMS       (AXI_ITEMS),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .TUSER_WIDTH (AXI_RCUSER_WIDTH)
    ) rc_axi[PCIE_ENDPOINTS](PCIE_USER_CLK);
    // For Intel and Xilinx (MFB)
    mfb_if #(
        .REGIONS (RQ_MFB_REGIONS),
        .REGION_SIZE (RQ_MFB_REGION_SIZE),
        .BLOCK_SIZE (RQ_MFB_BLOCK_SIZE),
        .ITEM_WIDTH (ITEM_WIDTH),
        .META_WIDTH (0)
    )  dma_rq_mfb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mvb_if #(
        .ITEMS (RQ_MFB_REGIONS),
        .ITEM_WIDTH (sv_dma_bus_pack::DMA_UPHDR_WIDTH)
    )                      dma_rq_mvb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mfb_if #(
        .REGIONS (RC_MFB_REGIONS),
        .REGION_SIZE (RC_MFB_REGION_SIZE),
        .BLOCK_SIZE (RC_MFB_BLOCK_SIZE),
        .ITEM_WIDTH (ITEM_WIDTH),
        .META_WIDTH (0)
    )  dma_rc_mfb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mvb_if #(
        .ITEMS (RC_MFB_REGIONS),
        .ITEM_WIDTH (sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)
    )                    dma_rc_mvb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);

    mfb_if #(
        .REGIONS (CQ_MFB_REGIONS),
        .REGION_SIZE (CQ_MFB_REGION_SIZE),
        .BLOCK_SIZE (CQ_MFB_BLOCK_SIZE),
        .ITEM_WIDTH (ITEM_WIDTH),
        .META_WIDTH (sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)
    )  dma_cq_mfb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mfb_if #(
        .REGIONS (CC_MFB_REGIONS),
        .REGION_SIZE (CC_MFB_REGION_SIZE),
        .BLOCK_SIZE (CC_MFB_BLOCK_SIZE),
        .ITEM_WIDTH (ITEM_WIDTH),
        .META_WIDTH (sv_pcie_meta_pack::PCIE_CC_META_WIDTH)
    )  dma_cc_mfb[PCIE_ENDPOINTS][DMA_PORTS](DMA_CLK);
    mi_if #(
        .DATA_WIDTH (32),
        .ADDR_WIDTH (32)
    ) config_mi[PCIE_ENDPOINTS] (MI_CLK);

    generate
        if (PCIE_ENDPOINTS == 1) begin : gen_PCIE_ENDPOINTS_1
            bind PCIE_TRANSACTION_CTRL : DUT_U.VHDL_DUT_U.pcie_ctrl_g[0].pcie_ctrl_i.ptc_g.ptc_i
                probe_inf #(MVB_UP_ITEMS * (1 + PCIE_TAG_WIDTH + sv_dma_bus_pack::DMA_UPHDR_WIDTH)) probe_tag (
                            .event_signal({tagm_mvb_out_src_rdy & tagm_mvb_out_dst_rdy}),
                            .event_data  ({tagm_mvb_out, tagm_mvb_out_tag, tagm_mvb_out_vld}),
                            .CLK         (CLK)
                        );
        end else if (PCIE_ENDPOINTS == 2) begin : gen_PCIE_ENDPOINTS_2
            bind PCIE_TRANSACTION_CTRL : DUT_U.VHDL_DUT_U.pcie_ctrl_g[0].pcie_ctrl_i.ptc_g.ptc_i
                probe_inf #(MVB_UP_ITEMS * (1 + PCIE_TAG_WIDTH + sv_dma_bus_pack::DMA_UPHDR_WIDTH)) probe_tag (
                            .event_signal({tagm_mvb_out_src_rdy & tagm_mvb_out_dst_rdy}),
                            .event_data  ({tagm_mvb_out, tagm_mvb_out_tag, tagm_mvb_out_vld}),
                            .CLK         (CLK)
                        );
            bind PCIE_TRANSACTION_CTRL : DUT_U.VHDL_DUT_U.pcie_ctrl_g[1].pcie_ctrl_i.ptc_g.ptc_i
                probe_inf #(MVB_UP_ITEMS * (1 + PCIE_TAG_WIDTH + sv_dma_bus_pack::DMA_UPHDR_WIDTH)) probe_tag (
                            .event_signal({tagm_mvb_out_src_rdy & tagm_mvb_out_dst_rdy}),
                            .event_data  ({tagm_mvb_out, tagm_mvb_out_tag, tagm_mvb_out_vld}),
                            .CLK         (CLK)
                        );
        end else begin : gen_line_74
            $error(
                "\nERROR: Unsupported combination (the Versal PCIE_CORE supports 1 or 2 PCIe endpoints)\n"
            );
        end
    endgenerate

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Define clock period
    always begin
        #(PCIE_SYSCLK_CLK_PERIOD) PCIE_SYSCLK_P = ~PCIE_SYSCLK_P;
    end
    always begin
        #(PCIE_SYSCLK_CLK_PERIOD) PCIE_SYSCLK_N = ~PCIE_SYSCLK_N;
    end
    always begin
        #(DMA_CLK_PERIOD) PCIE_USER_CLK         = ~PCIE_USER_CLK;
    end
    always begin
        #(DMA_CLK_PERIOD) DMA_CLK               = ~DMA_CLK;
    end
    always begin
        #(MI_CLK_PERIOD) MI_CLK                 = ~MI_CLK;
    end

    for (genvar pcie_e = 0; pcie_e < PCIE_ENDPOINTS; pcie_e++) begin : gen_pcie_e
        assign pcie_user_reset[pcie_e].RESET = pcie_user_reset_logic[pcie_e];
    end

    for (genvar pcie_clks = 0; pcie_clks < PCIE_CONS*PCIE_CLKS; pcie_clks++) begin : gen_pcie_clks
        assign pcie_sysclk_p_logic[pcie_clks] = PCIE_SYSCLK_P;
        assign pcie_sysclk_n_logic[pcie_clks] = PCIE_SYSCLK_N;
    end
    for (genvar pcie_c = 0; pcie_c < PCIE_CONS; pcie_c++) begin : gen_pcie_c
        assign pcie_sysrst_n_logic[pcie_c] = pcie_sysrst_n[pcie_c].RESET;
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // Start of tests
    initial begin
        uvm_root m_root;
        // DMA
        automatic virtual mfb_if #(
            .REGIONS (RQ_MFB_REGIONS),
            .REGION_SIZE (RQ_MFB_REGION_SIZE),
            .BLOCK_SIZE (RQ_MFB_BLOCK_SIZE),
            .ITEM_WIDTH (ITEM_WIDTH),
            .META_WIDTH (0)
        ) v_rq_mfb[PCIE_ENDPOINTS][DMA_PORTS] = dma_rq_mfb;
        automatic virtual mvb_if #(
            .ITEMS (RQ_MFB_REGIONS),
            .ITEM_WIDTH (sv_dma_bus_pack::DMA_UPHDR_WIDTH)
        )                                 v_rq_mvb[PCIE_ENDPOINTS][DMA_PORTS] = dma_rq_mvb;
        automatic virtual mfb_if #(
            .REGIONS (RC_MFB_REGIONS),
            .REGION_SIZE (RC_MFB_REGION_SIZE),
            .BLOCK_SIZE (RC_MFB_BLOCK_SIZE),
            .ITEM_WIDTH (ITEM_WIDTH),
            .META_WIDTH (0)
        ) v_rc_mfb[PCIE_ENDPOINTS][DMA_PORTS] = dma_rc_mfb;
        automatic virtual mvb_if #(
            .ITEMS (RC_MFB_REGIONS),
            .ITEM_WIDTH (sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)
        )                               v_rc_mvb[PCIE_ENDPOINTS][DMA_PORTS] = dma_rc_mvb;

        automatic virtual mfb_if #(
            .REGIONS (CQ_MFB_REGIONS),
            .REGION_SIZE (CQ_MFB_REGION_SIZE),
            .BLOCK_SIZE (CQ_MFB_BLOCK_SIZE),
            .ITEM_WIDTH (ITEM_WIDTH),
            .META_WIDTH (sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)
        ) v_cq_mfb[PCIE_ENDPOINTS][DMA_PORTS] = dma_cq_mfb;
        automatic virtual mfb_if #(
            .REGIONS (CC_MFB_REGIONS),
            .REGION_SIZE (CC_MFB_REGION_SIZE),
            .BLOCK_SIZE (CC_MFB_BLOCK_SIZE),
            .ITEM_WIDTH (ITEM_WIDTH),
            .META_WIDTH (sv_pcie_meta_pack::PCIE_CC_META_WIDTH)
        ) v_cc_mfb[PCIE_ENDPOINTS][DMA_PORTS] = dma_cc_mfb;

        // AXI
        automatic virtual axi_if #(
            .ITEMS       (AXI_ITEMS),
            .ITEM_WIDTH  (ITEM_WIDTH),
            .TUSER_WIDTH (AXI_CQUSER_WIDTH)
        ) v_cq_axi[PCIE_ENDPOINTS] = cq_axi;
        automatic virtual axi_if #(
            .ITEMS       (AXI_ITEMS),
            .ITEM_WIDTH  (ITEM_WIDTH),
            .TUSER_WIDTH (AXI_CCUSER_WIDTH)
        ) v_cc_axi[PCIE_ENDPOINTS] = cc_axi;
        automatic virtual axi_if #(
            .ITEMS       (AXI_ITEMS),
            .ITEM_WIDTH  (ITEM_WIDTH),
            .TUSER_WIDTH (AXI_RQUSER_WIDTH)
        ) v_rq_axi[PCIE_ENDPOINTS] = rq_axi;
        automatic virtual axi_if #(
            .ITEMS       (AXI_ITEMS),
            .ITEM_WIDTH  (ITEM_WIDTH),
            .TUSER_WIDTH (AXI_RCUSER_WIDTH)
        ) v_rc_axi[PCIE_ENDPOINTS] = rc_axi;

        automatic virtual mi_if #(
            .DATA_WIDTH (32),
            .ADDR_WIDTH (32)
        ) v_mi_config[PCIE_ENDPOINTS]       = config_mi;
        automatic virtual reset_if v_pcie_user_reset[PCIE_ENDPOINTS] = pcie_user_reset;
        automatic virtual reset_if v_pcie_sysrst_n[PCIE_CONS]        = pcie_sysrst_n;

        for (int unsigned pcie_c = 0; pcie_c < PCIE_CONS; pcie_c++) begin
            uvm_config_db#(virtual reset_if)::set(null, "", $sformatf("vif_pcie_sysrst_n_%0d", pcie_c),
                                                  v_pcie_sysrst_n[pcie_c]);
        end

        for (int unsigned pcie_e = 0; pcie_e < PCIE_ENDPOINTS; pcie_e++) begin
            string i_string;
            i_string.itoa(pcie_e);
            uvm_config_db#(virtual mi_if #(
                .DATA_WIDTH (32),
                .ADDR_WIDTH (32)
            ))::set(null, "", {"vif_mi_",i_string}, v_mi_config[pcie_e]);
            uvm_config_db #(virtual reset_if)::set(null, "", {"vif_pcie_user_reset_", i_string},
                                                  v_pcie_user_reset[pcie_e]);

            // AXI
            uvm_config_db#(virtual axi_if #(
                .ITEMS       (AXI_ITEMS),
                .ITEM_WIDTH  (ITEM_WIDTH),
                .TUSER_WIDTH (AXI_CQUSER_WIDTH)
            ))::set(null, "", {"vif_pcie_", i_string, "_cq_axi"}, v_cq_axi[pcie_e]);
            uvm_config_db#(virtual axi_if #(
                .ITEMS       (AXI_ITEMS),
                .ITEM_WIDTH  (ITEM_WIDTH),
                .TUSER_WIDTH (AXI_CCUSER_WIDTH)
            ))::set(null, "", {"vif_pcie_", i_string, "_cc_axi"}, v_cc_axi[pcie_e]);
            uvm_config_db#(virtual axi_if #(
                .ITEMS       (AXI_ITEMS),
                .ITEM_WIDTH  (ITEM_WIDTH),
                .TUSER_WIDTH (AXI_RQUSER_WIDTH)
            ))::set(null, "", {"vif_pcie_", i_string, "_rq_axi"}, v_rq_axi[pcie_e]);
            uvm_config_db#(virtual axi_if #(
                .ITEMS       (AXI_ITEMS),
                .ITEM_WIDTH  (ITEM_WIDTH),
                .TUSER_WIDTH (AXI_RCUSER_WIDTH)
            ))::set(null, "", {"vif_pcie_", i_string, "_rc_axi"}, v_rc_axi[pcie_e]);

            for (int dma = 0; dma < DMA_PORTS; dma++) begin
                string dma_string;
                dma_string = $sformatf("%0d_%0d", pcie_e, dma);
                uvm_config_db#(virtual mfb_if #(
                    .REGIONS (RQ_MFB_REGIONS),
                    .REGION_SIZE (RQ_MFB_REGION_SIZE),
                    .BLOCK_SIZE (RQ_MFB_BLOCK_SIZE),
                    .ITEM_WIDTH (ITEM_WIDTH),
                    .META_WIDTH (0)
                ))::set(null, "", {"vif_dma_",dma_string, "_rq_mfb"}, v_rq_mfb[pcie_e][dma]);
                uvm_config_db#(virtual mvb_if #(
                    .ITEMS (RQ_MFB_REGIONS),
                    .ITEM_WIDTH (sv_dma_bus_pack::DMA_UPHDR_WIDTH)
                ))::set(null, "", {"vif_dma_", dma_string, "_rq_mvb"}, v_rq_mvb[pcie_e][dma]);
                uvm_config_db#(virtual mfb_if #(
                    .REGIONS (RC_MFB_REGIONS),
                    .REGION_SIZE (RC_MFB_REGION_SIZE),
                    .BLOCK_SIZE (RC_MFB_BLOCK_SIZE),
                    .ITEM_WIDTH (ITEM_WIDTH),
                    .META_WIDTH (0)
                ))::set(null, "", {"vif_dma_",dma_string, "_rc_mfb"}, v_rc_mfb[pcie_e][dma]);
                uvm_config_db#(virtual mvb_if #(
                    .ITEMS (RC_MFB_REGIONS),
                    .ITEM_WIDTH (sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)
                ))::set(null, "", {"vif_dma_",dma_string, "_rc_mvb"}, v_rc_mvb[pcie_e][dma]);

                uvm_config_db#(virtual mfb_if #(
                    .REGIONS (CQ_MFB_REGIONS),
                    .REGION_SIZE (CQ_MFB_REGION_SIZE),
                    .BLOCK_SIZE (CQ_MFB_BLOCK_SIZE),
                    .ITEM_WIDTH (ITEM_WIDTH),
                    .META_WIDTH (sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)
                ))::set(null, "", {"vif_dma_cq_",dma_string, "_mfb"}, v_cq_mfb[pcie_e][dma]);
                uvm_config_db#(virtual mfb_if #(
                    .REGIONS (CC_MFB_REGIONS),
                    .REGION_SIZE (CC_MFB_REGION_SIZE),
                    .BLOCK_SIZE (CC_MFB_BLOCK_SIZE),
                    .ITEM_WIDTH (ITEM_WIDTH),
                    .META_WIDTH (sv_pcie_meta_pack::PCIE_CC_META_WIDTH)
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
            uvm_pcie_axi::root#(
                .AXI_ITEMS  (AXI_ITEMS),
                .DEVICE     (DEVICE),
                .STRADDLING (STRADDLING)
            )::get_type(), "uvm_test_top.*"
        );

        run_test();
        $stop(2);
    end

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // dut
    dut #(
        .MISC_TOP2PCIE_WIDTH (MISC_TOP2PCIE_WIDTH),
        .MISC_PCIE2TOP_WIDTH (MISC_PCIE2TOP_WIDTH)
    ) DUT_U (
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
        .config_mi       (config_mi),
        .MISC_TOP2PCIE   (misc_top2pcie),
        .MISC_PCIE2TOP   (misc_pcie2top)
    );

    // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
    // CONNECTION OF THE PCIE IP CORE (CIPS) VIA THE MISC SIGNALS
    generate
        for (genvar pcie_e = 0; pcie_e < PCIE_ENDPOINTS; pcie_e++) begin : gen_pcie_e_misc
            // The PCIe connector (and its reset) of the endpoint
            localparam int unsigned PCIE_C = pcie_e*PCIE_CONS/PCIE_ENDPOINTS;

            assign misc_top2pcie[(pcie_e+1)*MISC_TOP2PCIE_WIDTH-1 -: MISC_TOP2PCIE_WIDTH] = misc_out[pcie_e];
            assign misc_in[pcie_e] = misc_pcie2top[(pcie_e+1)*MISC_PCIE2TOP_WIDTH-1 -: MISC_PCIE2TOP_WIDTH];

            // Clock, reset and link of the IP core
            assign misc_out[pcie_e].USER_CLK    = PCIE_USER_CLK;
            assign misc_out[pcie_e].USER_RESET  = pcie_sysrst_n[PCIE_C].RESET;
            assign misc_out[pcie_e].USER_LNK_UP = 1'b1;

            // CQ (IP core -> DUT)
            assign misc_out[pcie_e].M_AXIS_CQ_TDATA  = cq_axi[pcie_e].TDATA;
            assign misc_out[pcie_e].M_AXIS_CQ_TUSER  = cq_axi[pcie_e].TUSER;
            assign misc_out[pcie_e].M_AXIS_CQ_TLAST  = cq_axi[pcie_e].TLAST;
            assign misc_out[pcie_e].M_AXIS_CQ_TKEEP  = cq_axi[pcie_e].TKEEP;
            assign misc_out[pcie_e].M_AXIS_CQ_TVALID = cq_axi[pcie_e].TVALID;
            assign cq_axi[pcie_e].TREADY             = misc_in[pcie_e].M_AXIS_CQ_TREADY;

            // RC (IP core -> DUT)
            assign misc_out[pcie_e].M_AXIS_RC_TDATA  = rc_axi[pcie_e].TDATA;
            assign misc_out[pcie_e].M_AXIS_RC_TUSER  = rc_axi[pcie_e].TUSER;
            assign misc_out[pcie_e].M_AXIS_RC_TLAST  = rc_axi[pcie_e].TLAST;
            assign misc_out[pcie_e].M_AXIS_RC_TKEEP  = rc_axi[pcie_e].TKEEP;
            assign misc_out[pcie_e].M_AXIS_RC_TVALID = rc_axi[pcie_e].TVALID;
            assign rc_axi[pcie_e].TREADY             = misc_in[pcie_e].M_AXIS_RC_TREADY;

            // CC (DUT -> IP core)
            assign cc_axi[pcie_e].TDATA              = misc_in[pcie_e].S_AXIS_CC_TDATA;
            assign cc_axi[pcie_e].TUSER              = misc_in[pcie_e].S_AXIS_CC_TUSER;
            assign cc_axi[pcie_e].TLAST              = misc_in[pcie_e].S_AXIS_CC_TLAST;
            assign cc_axi[pcie_e].TKEEP              = misc_in[pcie_e].S_AXIS_CC_TKEEP;
            assign cc_axi[pcie_e].TVALID             = misc_in[pcie_e].S_AXIS_CC_TVALID;
            assign misc_out[pcie_e].S_AXIS_CC_TREADY = cc_axi[pcie_e].TREADY;

            // RQ (DUT -> IP core)
            assign rq_axi[pcie_e].TDATA              = misc_in[pcie_e].S_AXIS_RQ_TDATA;
            assign rq_axi[pcie_e].TUSER              = misc_in[pcie_e].S_AXIS_RQ_TUSER;
            assign rq_axi[pcie_e].TLAST              = misc_in[pcie_e].S_AXIS_RQ_TLAST;
            assign rq_axi[pcie_e].TKEEP              = misc_in[pcie_e].S_AXIS_RQ_TKEEP;
            assign rq_axi[pcie_e].TVALID             = misc_in[pcie_e].S_AXIS_RQ_TVALID;
            assign misc_out[pcie_e].S_AXIS_RQ_TREADY = rq_axi[pcie_e].TREADY;

            // Tag status of the IP core is not used by the DUT
            assign misc_out[pcie_e].CFG_STATUS_RQ_TAG0     = '0;
            assign misc_out[pcie_e].CFG_STATUS_RQ_TAG1     = '0;
            assign misc_out[pcie_e].CFG_STATUS_RQ_TAG2     = '0;
            assign misc_out[pcie_e].CFG_STATUS_RQ_TAG3     = '0;
            assign misc_out[pcie_e].CFG_STATUS_RQ_TAG_VLD0 = 1'b0;
            assign misc_out[pcie_e].CFG_STATUS_RQ_TAG_VLD1 = 1'b0;
            assign misc_out[pcie_e].CFG_STATUS_RQ_TAG_VLD2 = 1'b0;
            assign misc_out[pcie_e].CFG_STATUS_RQ_TAG_VLD3 = 1'b0;

            // Configuration status used by the DUT: link up (DL_UP), MPS 256 B, MRRS 512 B, RCB
            assign misc_out[pcie_e].CFG_STATUS_PHY_LINK_STATUS      = 2'b11;
            assign misc_out[pcie_e].CFG_STATUS_MAX_PAYLOAD          = 2'b01;
            assign misc_out[pcie_e].CFG_STATUS_MAX_READ_REQ         = 3'b010;
            assign misc_out[pcie_e].CFG_STATUS_RCB_STATUS           = RCB;
            // Configuration status not used by the DUT
            assign misc_out[pcie_e].CFG_STATUS_PHY_LINK_DOWN        = 1'b0;
            assign misc_out[pcie_e].CFG_STATUS_NEGOTIATED_WIDTH     = '0;
            assign misc_out[pcie_e].CFG_STATUS_CURRENT_SPEED        = '0;
            assign misc_out[pcie_e].CFG_STATUS_FUNCTION_STATUS      = '0;
            assign misc_out[pcie_e].CFG_STATUS_FUNCTION_POWER_STATE = '0;
            assign misc_out[pcie_e].CFG_STATUS_LINK_POWER_STATE     = '0;
            assign misc_out[pcie_e].CFG_STATUS_LOCAL_ERROR_VALID    = 1'b0;
            assign misc_out[pcie_e].CFG_STATUS_LOCAL_ERROR_OUT      = '0;
            assign misc_out[pcie_e].CFG_STATUS_LTSSM_STATE          = '0;
            assign misc_out[pcie_e].CFG_STATUS_RX_PM_STATE          = '0;
            assign misc_out[pcie_e].CFG_STATUS_TX_PM_STATE          = '0;

            // Flow control credits (debug counters of the DUT only)
            assign misc_out[pcie_e].CFG_FC_PH  = 8'h40;
            assign misc_out[pcie_e].CFG_FC_PD  = 12'h400;
            assign misc_out[pcie_e].CFG_FC_NPH = 8'h40;
            assign misc_out[pcie_e].CFG_FC_NPD = 12'h400;

            // Configuration extension interface is idle
            assign misc_out[pcie_e].CFG_EXT_READ_RECEIVED     = 1'b0;
            assign misc_out[pcie_e].CFG_EXT_WRITE_RECEIVED    = 1'b0;
            assign misc_out[pcie_e].CFG_EXT_REGISTER_NUMBER   = '0;
            assign misc_out[pcie_e].CFG_EXT_FUNCTION_NUMBER   = '0;
            assign misc_out[pcie_e].CFG_EXT_WRITE_DATA        = '0;
            assign misc_out[pcie_e].CFG_EXT_WRITE_BYTE_ENABLE = '0;
        end
    endgenerate

endmodule
