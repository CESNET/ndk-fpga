// dut.sv: Design under test 
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input  logic [PCIE_CONS*PCIE_CLKS-1 : 0] PCIE_SYSCLK_P,
    input  logic [PCIE_CONS*PCIE_CLKS-1 : 0] PCIE_SYSCLK_N,
    output logic [PCIE_ENDPOINTS-1 : 0]      PCIE_USER_CLK,
    output logic [PCIE_ENDPOINTS-1 : 0]      PCIE_USER_RESET,
    input  logic [PCIE_CONS-1 : 0]           PCIE_SYSRST_N,
    input  logic                             INIT_DONE_N,
    input  logic                             DMA_CLK,
    input  logic                             DMA_RESET,
    input  logic                             MI_CLK,
    input  logic                             MI_RESET,
    // For Intel and Xilinx
    mfb_if.dut_rx dma_rq_mfb[PCIE_ENDPOINTS][DMA_PORTS],
    mvb_if.dut_rx dma_rq_mvb[PCIE_ENDPOINTS][DMA_PORTS],
    mfb_if.dut_tx dma_rc_mfb[PCIE_ENDPOINTS][DMA_PORTS],
    mvb_if.dut_tx dma_rc_mvb[PCIE_ENDPOINTS][DMA_PORTS],
    mfb_if.dut_tx dma_cq_mfb[PCIE_ENDPOINTS][DMA_PORTS],
    mfb_if.dut_rx dma_cc_mfb[PCIE_ENDPOINTS][DMA_PORTS],
    mi_if.dut_master config_mi[PCIE_ENDPOINTS]
    );

    // MI BUS
    logic [PCIE_ENDPOINTS*32    -1 : 0] mi_dwr;
    logic [PCIE_ENDPOINTS*32    -1 : 0] mi_addr;
    logic [PCIE_ENDPOINTS*(32/8)-1 : 0] mi_be;
    logic [PCIE_ENDPOINTS       -1 : 0] mi_rd;
    logic [PCIE_ENDPOINTS       -1 : 0] mi_wr;
    logic [PCIE_ENDPOINTS*32    -1 : 0] mi_drd;
    logic [PCIE_ENDPOINTS       -1 : 0] mi_ardy;
    logic [PCIE_ENDPOINTS       -1 : 0] mi_drdy;

    logic [PCIE_CONS*PCIE_LANES-1 : 0] pcie_txp;
    logic [PCIE_CONS*PCIE_LANES-1 : 0] pcie_txn;

    // RQ BUS
    logic [PCIE_ENDPOINTS*DMA_PORTS*RQ_MFB_REGIONS*RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE*ITEM_WIDTH                            -1 : 0] dma_rq_mfb_data;
    logic [PCIE_ENDPOINTS*DMA_PORTS*RQ_MFB_REGIONS*RQ_MFB_META_W                                                              -1 : 0] dma_rq_mfb_meta;
    logic [PCIE_ENDPOINTS*DMA_PORTS*RQ_MFB_REGIONS                                                                            -1 : 0] dma_rq_mfb_sof;
    logic [PCIE_ENDPOINTS*DMA_PORTS*RQ_MFB_REGIONS                                                                            -1 : 0] dma_rq_mfb_eof;
    logic [PCIE_ENDPOINTS*DMA_PORTS*((RQ_MFB_REGION_SIZE != 1) ? RQ_MFB_REGIONS*$clog2(RQ_MFB_REGION_SIZE) : RQ_MFB_REGIONS*1)-1 : 0] dma_rq_mfb_sof_pos;
    logic [PCIE_ENDPOINTS*DMA_PORTS*RQ_MFB_REGIONS*$clog2(RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE)                               -1 : 0] dma_rq_mfb_eof_pos;
    logic [PCIE_ENDPOINTS*DMA_PORTS                                                                                           -1 : 0] dma_rq_mfb_src_rdy;
    logic [PCIE_ENDPOINTS*DMA_PORTS                                                                                           -1 : 0] dma_rq_mfb_dst_rdy;

    logic [PCIE_ENDPOINTS*DMA_PORTS*RQ_MFB_REGIONS*sv_dma_bus_pack::DMA_UPHDR_WIDTH                                          -1 : 0] dma_rq_mvb_data;
    logic [PCIE_ENDPOINTS*DMA_PORTS*RQ_MFB_REGIONS                                                                            -1 : 0] dma_rq_mvb_vld;
    logic [PCIE_ENDPOINTS*DMA_PORTS                                                                                           -1 : 0] dma_rq_mvb_src_rdy;
    logic [PCIE_ENDPOINTS*DMA_PORTS                                                                                           -1 : 0] dma_rq_mvb_dst_rdy;

    // RC BUS
    logic [PCIE_ENDPOINTS*DMA_PORTS*RC_MFB_REGIONS*RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE*ITEM_WIDTH                            -1 : 0] dma_rc_mfb_data;
    logic [PCIE_ENDPOINTS*DMA_PORTS*RC_MFB_REGIONS*RC_MFB_META_W                                                              -1 : 0] dma_rc_mfb_meta;
    logic [PCIE_ENDPOINTS*DMA_PORTS*RC_MFB_REGIONS                                                                            -1 : 0] dma_rc_mfb_sof;
    logic [PCIE_ENDPOINTS*DMA_PORTS*RC_MFB_REGIONS                                                                            -1 : 0] dma_rc_mfb_eof;
    logic [PCIE_ENDPOINTS*DMA_PORTS*((RC_MFB_REGION_SIZE != 1) ? RC_MFB_REGIONS*$clog2(RC_MFB_REGION_SIZE) : RC_MFB_REGIONS*1)-1 : 0] dma_rc_mfb_sof_pos;
    logic [PCIE_ENDPOINTS*DMA_PORTS*RC_MFB_REGIONS*$clog2(RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE)                               -1 : 0] dma_rc_mfb_eof_pos;
    logic [PCIE_ENDPOINTS*DMA_PORTS                                                                                           -1 : 0] dma_rc_mfb_src_rdy;
    logic [PCIE_ENDPOINTS*DMA_PORTS                                                                                           -1 : 0] dma_rc_mfb_dst_rdy;

    logic [PCIE_ENDPOINTS*DMA_PORTS*RC_MFB_REGIONS*sv_dma_bus_pack::DMA_DOWNHDR_WIDTH                                         -1 : 0] dma_rc_mvb_data;
    logic [PCIE_ENDPOINTS*DMA_PORTS*RC_MFB_REGIONS                                                                            -1 : 0] dma_rc_mvb_vld;
    logic [PCIE_ENDPOINTS*DMA_PORTS                                                                                           -1 : 0] dma_rc_mvb_src_rdy;
    logic [PCIE_ENDPOINTS*DMA_PORTS                                                                                           -1 : 0] dma_rc_mvb_dst_rdy;

    // CC BUS
    logic [PCIE_ENDPOINTS*DMA_PORTS*CC_MFB_REGIONS*CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE*ITEM_WIDTH                            -1 : 0] dma_cc_mfb_data;
    logic [PCIE_ENDPOINTS*DMA_PORTS*CC_MFB_REGIONS*CC_MFB_META_W                                                              -1 : 0] dma_cc_mfb_meta;
    logic [PCIE_ENDPOINTS*DMA_PORTS*CC_MFB_REGIONS                                                                            -1 : 0] dma_cc_mfb_sof;
    logic [PCIE_ENDPOINTS*DMA_PORTS*CC_MFB_REGIONS                                                                            -1 : 0] dma_cc_mfb_eof;
    logic [PCIE_ENDPOINTS*DMA_PORTS*((CC_MFB_REGION_SIZE != 1) ? CC_MFB_REGIONS*$clog2(CC_MFB_REGION_SIZE) : CC_MFB_REGIONS*1)-1 : 0] dma_cc_mfb_sof_pos;
    logic [PCIE_ENDPOINTS*DMA_PORTS*CC_MFB_REGIONS*$clog2(CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE)                               -1 : 0] dma_cc_mfb_eof_pos;
    logic [PCIE_ENDPOINTS*DMA_PORTS                                                                                           -1 : 0] dma_cc_mfb_src_rdy;
    logic [PCIE_ENDPOINTS*DMA_PORTS                                                                                           -1 : 0] dma_cc_mfb_dst_rdy;

    // CQ BUS
    logic [PCIE_ENDPOINTS*DMA_PORTS*CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*ITEM_WIDTH                            -1 : 0] dma_cq_mfb_data;
    logic [PCIE_ENDPOINTS*DMA_PORTS*CQ_MFB_REGIONS*CQ_MFB_META_W                                                              -1 : 0] dma_cq_mfb_meta;
    logic [PCIE_ENDPOINTS*DMA_PORTS*CQ_MFB_REGIONS                                                                            -1 : 0] dma_cq_mfb_sof;
    logic [PCIE_ENDPOINTS*DMA_PORTS*CQ_MFB_REGIONS                                                                            -1 : 0] dma_cq_mfb_eof;
    logic [PCIE_ENDPOINTS*DMA_PORTS*((CQ_MFB_REGION_SIZE != 1) ? CQ_MFB_REGIONS*$clog2(CQ_MFB_REGION_SIZE) : CQ_MFB_REGIONS*1)-1 : 0] dma_cq_mfb_sof_pos;
    logic [PCIE_ENDPOINTS*DMA_PORTS*CQ_MFB_REGIONS*$clog2(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE)                               -1 : 0] dma_cq_mfb_eof_pos;
    logic [PCIE_ENDPOINTS*DMA_PORTS                                                                                           -1 : 0] dma_cq_mfb_src_rdy;
    logic [PCIE_ENDPOINTS*DMA_PORTS                                                                                           -1 : 0] dma_cq_mfb_dst_rdy;

    for (genvar pcie = 0; pcie < PCIE_ENDPOINTS; pcie++) begin
        for (genvar dma = 0; dma < DMA_PORTS; dma++) begin
            localparam int unsigned dma_it = pcie*DMA_PORTS +  dma;

            for (genvar dma_region = 0; dma_region < RQ_MFB_REGIONS; dma_region++) begin
                assign dma_rq_mvb_vld[dma_it*RQ_MFB_REGIONS + dma_region] = dma_rq_mvb[pcie][dma].VLD[dma_region];
            end
            for (genvar dma_region = 0; dma_region < RC_MFB_REGIONS; dma_region++) begin
                assign dma_rc_mvb[pcie][dma].VLD[dma_region] = dma_rc_mvb_vld[dma_it*RC_MFB_REGIONS + dma_region];
            end

            assign dma_rq_mfb_data[(dma_it+1)*RQ_MFB_REGIONS*RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE*ITEM_WIDTH-1 -: RQ_MFB_REGIONS*RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE*ITEM_WIDTH]       = dma_rq_mfb[pcie][dma].DATA;
            assign dma_rq_mfb_meta[(dma_it+1)*RQ_MFB_REGIONS*RQ_MFB_META_W                                         -1 -: RQ_MFB_REGIONS*RQ_MFB_META_W]                                  = dma_rq_mfb[pcie][dma].META;
            assign dma_rq_mfb_sof[(dma_it+1)*RQ_MFB_REGIONS                                                        -1 -: RQ_MFB_REGIONS]                                                = dma_rq_mfb[pcie][dma].SOF;
            assign dma_rq_mfb_eof[(dma_it+1)*RQ_MFB_REGIONS                                                        -1 -: RQ_MFB_REGIONS]                                                = dma_rq_mfb[pcie][dma].EOF;
            if (RQ_MFB_REGION_SIZE > 1) begin
                assign dma_rq_mfb_sof_pos[(dma_it+1)*RQ_MFB_REGIONS*$clog2(RQ_MFB_REGION_SIZE)                     -1 -: RQ_MFB_REGIONS*$clog2(RQ_MFB_REGION_SIZE)]                     = dma_rq_mfb[pcie][dma].SOF_POS;
            end
            assign dma_rq_mfb_eof_pos[(dma_it+1)*RQ_MFB_REGIONS*$clog2(RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE)       -1 -: RQ_MFB_REGIONS*$clog2(RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE)]   = dma_rq_mfb[pcie][dma].EOF_POS;
            assign dma_rq_mfb_src_rdy[dma_it]                                                                                                                                           = dma_rq_mfb[pcie][dma].SRC_RDY;
            assign dma_rq_mfb[pcie][dma].DST_RDY                                                                                                                                           = dma_rq_mfb_dst_rdy[dma_it];

            assign dma_rq_mvb_data[(dma_it+1)*RQ_MFB_REGIONS*sv_dma_bus_pack::DMA_UPHDR_WIDTH                      -1 -: RQ_MFB_REGIONS*sv_dma_bus_pack::DMA_UPHDR_WIDTH]               = dma_rq_mvb[pcie][dma].DATA;
            assign dma_rq_mvb_src_rdy[dma_it]                                                                                                                                           = dma_rq_mvb[pcie][dma].SRC_RDY;
            assign dma_rq_mvb[pcie][dma].DST_RDY                                                                                                                                           = dma_rq_mvb_dst_rdy[dma_it];

            assign dma_cc_mfb_data[(dma_it+1)*CC_MFB_REGIONS*CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE*ITEM_WIDTH-1 -: CC_MFB_REGIONS*CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE*ITEM_WIDTH] = dma_cc_mfb[pcie][dma].DATA;
            assign dma_cc_mfb_meta[(dma_it+1)*CC_MFB_REGIONS*CC_MFB_META_W                                         -1 -: CC_MFB_REGIONS*CC_MFB_META_W]                            = dma_cc_mfb[pcie][dma].META;
            assign dma_cc_mfb_sof[(dma_it+1)*CC_MFB_REGIONS                                                        -1 -: CC_MFB_REGIONS]                                          = dma_cc_mfb[pcie][dma].SOF;
            assign dma_cc_mfb_eof[(dma_it+1)*CC_MFB_REGIONS                                                        -1 -: CC_MFB_REGIONS]                                          = dma_cc_mfb[pcie][dma].EOF;
            if (RQ_MFB_REGION_SIZE > 1) begin
                assign dma_cc_mfb_sof_pos[(dma_it+1)*CC_MFB_REGIONS*$clog2(CC_MFB_REGION_SIZE)                         -1 -: CC_MFB_REGIONS*$clog2(CC_MFB_REGION_SIZE)]           = dma_cc_mfb[pcie][dma].SOF_POS;
            end
            assign dma_cc_mfb_eof_pos[(dma_it+1)*CC_MFB_REGIONS*$clog2(CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE)       -1 -: CC_MFB_REGIONS*$clog2(CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE)]           = dma_cc_mfb[pcie][dma].EOF_POS;
            assign dma_cc_mfb_src_rdy[dma_it]                                                                                                                                                   = dma_cc_mfb[pcie][dma].SRC_RDY;
            assign dma_cc_mfb[pcie][dma].DST_RDY                                                                                                                                                   = dma_cc_mfb_dst_rdy[dma_it];

            assign dma_rc_mfb[pcie][dma].DATA    = dma_rc_mfb_data[(dma_it+1)*RC_MFB_REGIONS*RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE*ITEM_WIDTH-1 -: RC_MFB_REGIONS*RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE*ITEM_WIDTH];
            assign dma_rc_mfb[pcie][dma].META    = dma_rc_mfb_meta[(dma_it+1)*RC_MFB_REGIONS*RC_MFB_META_W                                         -1 -: RC_MFB_REGIONS*RC_MFB_META_W];
            assign dma_rc_mfb[pcie][dma].SOF     = dma_rc_mfb_sof[(dma_it+1)*RC_MFB_REGIONS                                                        -1 -: RC_MFB_REGIONS];
            assign dma_rc_mfb[pcie][dma].EOF     = dma_rc_mfb_eof[(dma_it+1)*RC_MFB_REGIONS                                                        -1 -: RC_MFB_REGIONS];
            if (RQ_MFB_REGION_SIZE > 1) begin
                assign dma_rc_mfb[pcie][dma].SOF_POS = dma_rc_mfb_sof_pos[(dma_it+1)*RC_MFB_REGIONS*$clog2(RC_MFB_REGION_SIZE)                         -1 -: RC_MFB_REGIONS*$clog2(RC_MFB_REGION_SIZE)];
            end
            assign dma_rc_mfb[pcie][dma].EOF_POS = dma_rc_mfb_eof_pos[(dma_it+1)*RC_MFB_REGIONS*$clog2(RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE)       -1 -: RC_MFB_REGIONS*$clog2(RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE)];
            assign dma_rc_mfb[pcie][dma].SRC_RDY = dma_rc_mfb_src_rdy[dma_it];
            assign dma_rc_mfb_dst_rdy[dma_it] = dma_rc_mfb[pcie][dma].DST_RDY;

            assign dma_rc_mvb[pcie][dma].DATA    = dma_rc_mvb_data[(dma_it+1)*RC_MFB_REGIONS*sv_dma_bus_pack::DMA_DOWNHDR_WIDTH                    -1 -: RC_MFB_REGIONS*sv_dma_bus_pack::DMA_DOWNHDR_WIDTH];
            assign dma_rc_mvb[pcie][dma].SRC_RDY = dma_rc_mvb_src_rdy[dma_it];
            assign dma_rc_mvb_dst_rdy[dma_it] = dma_rc_mvb[pcie][dma].DST_RDY;

            assign dma_cq_mfb[pcie][dma].DATA    = dma_cq_mfb_data[(dma_it+1)*CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*ITEM_WIDTH-1 -: CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*ITEM_WIDTH];
            assign dma_cq_mfb[pcie][dma].META    = dma_cq_mfb_meta[(dma_it+1)*CQ_MFB_REGIONS*CQ_MFB_META_W                                         -1 -: CQ_MFB_REGIONS*CQ_MFB_META_W];
            assign dma_cq_mfb[pcie][dma].SOF     = dma_cq_mfb_sof[(dma_it+1)*CQ_MFB_REGIONS                                                        -1 -: CQ_MFB_REGIONS];
            assign dma_cq_mfb[pcie][dma].EOF     = dma_cq_mfb_eof[(dma_it+1)*CQ_MFB_REGIONS                                                        -1 -: CQ_MFB_REGIONS];
            if (RQ_MFB_REGION_SIZE > 1) begin
                assign dma_cq_mfb[pcie][dma].SOF_POS = dma_cq_mfb_sof_pos[(dma_it+1)*CQ_MFB_REGIONS*$clog2(CQ_MFB_REGION_SIZE)                         -1 -: CQ_MFB_REGIONS*$clog2(CQ_MFB_REGION_SIZE)];
            end
            assign dma_cq_mfb[pcie][dma].EOF_POS = dma_cq_mfb_eof_pos[(dma_it+1)*CQ_MFB_REGIONS*$clog2(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE)       -1 -: CQ_MFB_REGIONS*$clog2(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE)];
            assign dma_cq_mfb[pcie][dma].SRC_RDY = dma_cq_mfb_src_rdy[dma_it];
            assign dma_cq_mfb_dst_rdy[dma_it] = dma_cq_mfb[pcie][dma].DST_RDY;
        end

        assign config_mi[pcie].DWR            = mi_dwr[(pcie+1)*32   -1 -: 32];
        assign config_mi[pcie].ADDR           = mi_addr[(pcie+1)*32  -1 -: 32];
        assign config_mi[pcie].BE             = mi_be[(pcie+1)*(32/8)-1 -: (32/8)];
        assign config_mi[pcie].RD             = mi_rd[pcie];
        assign config_mi[pcie].WR             = mi_wr[pcie];
        assign mi_drd[(pcie+1)*32   -1 -: 32] = config_mi[pcie].DRD;
        assign mi_ardy[pcie]                  = config_mi[pcie].ARDY;
        assign mi_drdy[pcie]                  = config_mi[pcie].DRDY;
    end

    PCIE #(
        // =====================================================================
        // BAR base address configuration
        // =====================================================================
        .BAR0_BASE_ADDR     (BAR0_BASE_ADDR),
        .BAR1_BASE_ADDR     (BAR1_BASE_ADDR),
        .BAR2_BASE_ADDR     (BAR2_BASE_ADDR),
        .BAR3_BASE_ADDR     (BAR3_BASE_ADDR),
        .BAR4_BASE_ADDR     (BAR4_BASE_ADDR),
        .BAR5_BASE_ADDR     (BAR5_BASE_ADDR),
        .EXP_ROM_BASE_ADDR  (EXP_ROM_BASE_ADDR),

        // =====================================================================
        // MFB configuration
        // =====================================================================
        // CQ MFB
        .CQ_MFB_REGIONS     (CQ_MFB_REGIONS),
        .CQ_MFB_REGION_SIZE (CQ_MFB_REGION_SIZE),
        .CQ_MFB_BLOCK_SIZE  (CQ_MFB_BLOCK_SIZE),
        .CQ_MFB_ITEM_WIDTH  (ITEM_WIDTH),
        // RC MFB
        .RC_MFB_REGIONS     (RC_MFB_REGIONS),
        .RC_MFB_REGION_SIZE (RC_MFB_REGION_SIZE),
        .RC_MFB_BLOCK_SIZE  (RC_MFB_BLOCK_SIZE),
        .RC_MFB_ITEM_WIDTH  (ITEM_WIDTH),
        // CC MFB
        .CC_MFB_REGIONS     (CC_MFB_REGIONS),
        .CC_MFB_REGION_SIZE (CC_MFB_REGION_SIZE),
        .CC_MFB_BLOCK_SIZE  (CC_MFB_BLOCK_SIZE),
        .CC_MFB_ITEM_WIDTH  (ITEM_WIDTH),
        // RQ MFB
        .RQ_MFB_REGIONS     (RQ_MFB_REGIONS),
        .RQ_MFB_REGION_SIZE (RQ_MFB_REGION_SIZE),
        .RQ_MFB_BLOCK_SIZE  (RQ_MFB_BLOCK_SIZE),
        .RQ_MFB_ITEM_WIDTH  (ITEM_WIDTH),

        // =====================================================================
        // PCIE configuration
        // =====================================================================
        // Total number of DMA_EP, DMA_EP=PCIE_EP or 2*DMA_EP=PCIE_EP
        .DMA_PORTS          (PCIE_ENDPOINTS*DMA_PORTS),
        // Connected PCIe endpoint type
        .PCIE_ENDPOINT_TYPE (PCIE_ENDPOINT_TYPE),
        // PCIe Endpoint (EP) mode: 0=x16, 1=x8x8, 2=x8
        .PCIE_ENDPOINT_MODE (PCIE_ENDPOINT_MODE),
        // Number of PCIe endpoints
        .PCIE_ENDPOINTS     (PCIE_ENDPOINTS),
        // Number of PCIe clocks per PCIe connector
        .PCIE_CLKS          (PCIE_CLKS),
        // Number of PCIe connectors
        .PCIE_CONS          (PCIE_CONS),
        // Number of PCIe lanes in each PCIe connector
        .PCIE_LANES         (PCIE_LANES),

        // =====================================================================
        // Other configuration
        // =====================================================================
        // Width of CARD/FPGA ID number
        .CARD_ID_WIDTH      (CARD_ID_WIDTH),
        // Disable PTC module and allows direct connection of the DMA module to
        // the PCIe IP RQ and RC interfaces.
        .PTC_DISABLE        (PTC_DISABLE),
        // Enable CQ/CC interface for DMA-BAR, condition DMA_PORTS=PCIE_ENDPOINTS
        .DMA_BAR_ENABLE     (DMA_BAR_ENABLE),
        // Enable of XCV IP, for Xilinx only
        .XVC_ENABLE         (XVC_ENABLE),
        // FPGA device
        .DEVICE             (DEVICE)

    ) VHDL_DUT_U (
        // =====================================================================
        // CLOCKS AND RESETS
        // =====================================================================
        // Clock from PCIe port, 100 MHz
        .PCIE_SYSCLK_P       (PCIE_SYSCLK_P),
        .PCIE_SYSCLK_N       (PCIE_SYSCLK_N),
        // PCIe reset from PCIe port
        .PCIE_SYSRST_N       (PCIE_SYSRST_N),
        // nINIT_DONE output of the Reset Release Intel Stratix 10 FPGA IP
        .INIT_DONE_N         (INIT_DONE_N),
        // PCIe user clock and reset
        .PCIE_USER_CLK       (PCIE_USER_CLK),
        .PCIE_USER_RESET     (PCIE_USER_RESET),
        // DMA module clock and reset
        .DMA_CLK             (DMA_CLK),
        .DMA_RESET           (DMA_RESET),

        // =====================================================================
        // PCIE SERIAL INTERFACE
        // =====================================================================
        // Receive data
        .PCIE_RX_P           (pcie_txp),
        .PCIE_RX_N           (pcie_txn),
        // Transmit data
        .PCIE_TX_P           (pcie_txp),
        .PCIE_TX_N           (pcie_txn),

        // =====================================================================
        // Configuration status interface (PCIE_USER_CLK)
        // =====================================================================
        // PCIe link up flag per PCIe endpoint
        .PCIE_LINK_UP        (),
        // PCIe maximum payload size
        .PCIE_MPS            (),
        // PCIe maximum read request size
        .PCIE_MRRS           (),
        // PCIe extended tag enable (8-bit tag)
        .PCIE_EXT_TAG_EN     (),
        // PCIe 10-bit tag requester enable
        .PCIE_10B_TAG_REQ_EN (),
        // PCIe RCB size control
        .PCIE_RCB_SIZE       (),
        // Card ID / PCIe Device Serial Number
        .CARD_ID             (),

        // =====================================================================
        // DMA RQ MFB+MVB interface (PCIE_CLK or DMA_CLK)
        //
        // PTC ENABLE: MFB+MVB bus for transferring RQ PTC-DMA transactions.
        // MFB+MVB bus is clocked at DMA_CLK.
        // PTC DISABLE: MFB bus only for transferring RQ PCIe transactions 
        // (format according to the PCIe IP used). Compared to the standard MFB
        // specification, it does not allow gaps (SRC_RDY=0) inside transactions
        // and requires that the first transaction in a word starts at byte 0.
        // MFB bus is clocked at PCIE_CLK.
        // =====================================================================
        .DMA_RQ_MFB_DATA     (dma_rq_mfb_data),
        .DMA_RQ_MFB_META     (dma_rq_mfb_meta),
        .DMA_RQ_MFB_SOF      (dma_rq_mfb_sof),
        .DMA_RQ_MFB_EOF      (dma_rq_mfb_eof),
        .DMA_RQ_MFB_SOF_POS  (dma_rq_mfb_sof_pos),
        .DMA_RQ_MFB_EOF_POS  (dma_rq_mfb_eof_pos),
        .DMA_RQ_MFB_SRC_RDY  (dma_rq_mfb_src_rdy),
        .DMA_RQ_MFB_DST_RDY  (dma_rq_mfb_dst_rdy),

        .DMA_RQ_MVB_DATA     (dma_rq_mvb_data),
        .DMA_RQ_MVB_VLD      (dma_rq_mvb_vld),
        .DMA_RQ_MVB_SRC_RDY  (dma_rq_mvb_src_rdy),
        .DMA_RQ_MVB_DST_RDY  (dma_rq_mvb_dst_rdy),

        // =====================================================================
        // DMA RC MFB+MVB interface (PCIE_CLK or DMA_CLK)
        //
        // PTC ENABLE: MFB+MVB bus for transferring RC PTC-DMA transactions.
        // MFB+MVB bus is clocked at DMA_CLK.
        // PTC DISABLE: MFB bus only for transferring RC PCIe transactions 
        // (format according to the PCIe IP used). Compared to the standard MFB
        // specification, it does not allow gaps (SRC_RDY=0) inside transactions
        // and requires that the first transaction in a word starts at byte 0.
        // MFB bus is clocked at PCIE_CLK.
        // =====================================================================
        .DMA_RC_MFB_DATA     (dma_rc_mfb_data),
        .DMA_RC_MFB_META     (dma_rc_mfb_meta),
        .DMA_RC_MFB_SOF      (dma_rc_mfb_sof),
        .DMA_RC_MFB_EOF      (dma_rc_mfb_eof),
        .DMA_RC_MFB_SOF_POS  (dma_rc_mfb_sof_pos),
        .DMA_RC_MFB_EOF_POS  (dma_rc_mfb_eof_pos),
        .DMA_RC_MFB_SRC_RDY  (dma_rc_mfb_src_rdy),
        .DMA_RC_MFB_DST_RDY  (dma_rc_mfb_dst_rdy),

        .DMA_RC_MVB_DATA     (dma_rc_mvb_data),
        .DMA_RC_MVB_VLD      (dma_rc_mvb_vld),
        .DMA_RC_MVB_SRC_RDY  (dma_rc_mvb_src_rdy),
        .DMA_RC_MVB_DST_RDY  (dma_rc_mvb_dst_rdy),

        // =====================================================================
        // DMA CQ MFB interface - DMA-BAR (PCIE_CLK)
        //
        // MFB bus for transferring CQ DMA-BAR PCIe transactions (format
        // according to the PCIe IP used). Compared to the standard MFB
        // specification, it does not allow gaps (SRC_RDY=0) inside transactions
        // and requires that the first transaction in a word starts at byte 0.
        // =====================================================================
        .DMA_CQ_MFB_DATA     (dma_cq_mfb_data),
        .DMA_CQ_MFB_META     (dma_cq_mfb_meta),
        .DMA_CQ_MFB_SOF      (dma_cq_mfb_sof),
        .DMA_CQ_MFB_EOF      (dma_cq_mfb_eof),
        .DMA_CQ_MFB_SOF_POS  (dma_cq_mfb_sof_pos),
        .DMA_CQ_MFB_EOF_POS  (dma_cq_mfb_eof_pos),
        .DMA_CQ_MFB_SRC_RDY  (dma_cq_mfb_src_rdy),
        .DMA_CQ_MFB_DST_RDY  (dma_cq_mfb_dst_rdy),

        // =====================================================================
        // PCIE CC MFB interface - DMA-BAR (PCIE_CLK)
        //
        // MFB bus for transferring CC DMA-BAR PCIe transactions (format
        // according to the PCIe IP used). Compared to the standard MFB
        // specification, it does not allow gaps (SRC_RDY=0) inside transactions
        // and requires that the first transaction in a word starts at byte 0.
        // =====================================================================
        .DMA_CC_MFB_DATA     (dma_cc_mfb_data),
        .DMA_CC_MFB_META     (dma_cc_mfb_meta),
        .DMA_CC_MFB_SOF      (dma_cc_mfb_sof),
        .DMA_CC_MFB_EOF      (dma_cc_mfb_eof),
        .DMA_CC_MFB_SOF_POS  (dma_cc_mfb_sof_pos),
        .DMA_CC_MFB_EOF_POS  (dma_cc_mfb_eof_pos),
        .DMA_CC_MFB_SRC_RDY  (dma_cc_mfb_src_rdy),
        .DMA_CC_MFB_DST_RDY  (dma_cc_mfb_dst_rdy),

        // =====================================================================
        // MI32 interfaces (MI_CLK)
        //
        // Root of the MI32 bus tree for each PCIe endpoint
        // =====================================================================
        .MI_CLK              (MI_CLK),
        .MI_RESET            (MI_RESET),
        .MI_DWR              (mi_dwr),
        .MI_ADDR             (mi_addr),
        .MI_BE               (mi_be),
        .MI_RD               (mi_rd),
        .MI_WR               (mi_wr),
        .MI_DRD              (mi_drd),
        .MI_ARDY             (mi_ardy),
        .MI_DRDY             (mi_drdy)

    );


endmodule
