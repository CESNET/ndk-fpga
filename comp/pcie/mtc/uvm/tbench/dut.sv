//-- dut.sv: Design under test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT(
        input logic      CLK,
        input logic      RST,
        mfb_if.dut_rx    mfb_cq,
        mfb_if.dut_tx    mfb_cc,
        mi_if.dut_master config_mi
    );

    logic [3-1 : 0] ctl_max_payload_size;
    logic [8-1 : 0] mi_function;

    logic [((MFB_REGION_SIZE != 1) ? MFB_REGIONS*$clog2(MFB_REGION_SIZE) : MFB_REGIONS)-1 : 0] cq_sof_pos;
    logic [((MFB_REGION_SIZE != 1) ? MFB_REGIONS*$clog2(MFB_REGION_SIZE) : MFB_REGIONS)-1 : 0] cc_sof_pos;

    generate
        if (MFB_REGIONS*MFB_REGION_SIZE != 1) begin
            assign cq_sof_pos = mfb_cq.SOF_POS;
        end else
            assign cq_sof_pos = '0;
    endgenerate

    assign mfb_cc.SOF_POS = cc_sof_pos;

    generate
        if (BYTES_LEN_MAX == 128)
            assign ctl_max_payload_size = 3'b000;
        if (BYTES_LEN_MAX == 256)
            assign ctl_max_payload_size = 3'b001;
        if (BYTES_LEN_MAX == 512)
            assign ctl_max_payload_size = 3'b010;
        if (BYTES_LEN_MAX == 1024)
            assign ctl_max_payload_size = 3'b011;
        if (BYTES_LEN_MAX == 2048)
            assign ctl_max_payload_size = 3'b100;
        if (BYTES_LEN_MAX == 4096)
            assign ctl_max_payload_size = 3'b101;
    endgenerate

    MTC #(
        // MFB bus: number of regions in word
        .MFB_REGIONS       (MFB_REGIONS),
        // MFB bus: number of blocks in region, must be 1
        .MFB_REGION_SIZE   (MFB_REGION_SIZE),
        // MFB bus: number of items in block, must be 8
        .MFB_BLOCK_SIZE    (MFB_BLOCK_SIZE),
        // MFB bus: width of one item in bits, must be 32 (dword)
        .MFB_ITEM_WIDTH    (MFB_ITEM_WIDTH),
        // BAR0 base address for PCIE->MI32 transalation
        .BAR0_BASE_ADDR    (BAR0_BASE_ADDR),
        // BAR1 base address for PCIE->MI32 transalation
        .BAR1_BASE_ADDR    (BAR1_BASE_ADDR),
        // BAR2 base address for PCIE->MI32 transalation
        .BAR2_BASE_ADDR    (BAR2_BASE_ADDR),
        // BAR3 base address for PCIE->MI32 transalation
        .BAR3_BASE_ADDR    (BAR3_BASE_ADDR),
        // BAR4 base address for PCIE->MI32 transalation
        .BAR4_BASE_ADDR    (BAR4_BASE_ADDR),
        // BAR5 base address for PCIE->MI32 transalation
        .BAR5_BASE_ADDR    (BAR5_BASE_ADDR),
        // Expansion ROM base address for PCIE->MI32 transalation
        .EXP_ROM_BASE_ADDR (EXP_ROM_BASE_ADDR),
        // Enable Pipe component on CC interface
        .CC_PIPE           (CC_PIPE),
        // Enable Pipe component on CQ interface
        .CQ_PIPE           (CQ_PIPE),
        // Enable Pipe component on MI32 interface
        .MI_PIPE           (MI_PIPE),
        // MI bus: width of data word in bits, must be 32.
        .MI_DATA_WIDTH     (MI_DATA_WIDTH),
        // MI bus: width of address word in bits, must be 32.
        .MI_ADDR_WIDTH     (MI_ADDR_WIDTH),
        // Select correct FPGA device: "ULTRASCALE", "STRATIX10", "AGILEX"
        .DEVICE            (DEVICE),
        // Intel PCIe endpoint type:
        .ENDPOINT_TYPE     (ENDPOINT_TYPE)
    ) VHDL_DUT_U (
        .CLK                       (CLK),
        .RESET                     (RST),

        // =====================================================================
        // Configuration Status Interface
        // =====================================================================

        // Maximum allowed size of completion payload: 000b = 128 bytes;
        // 001b = 256 bytes; 010b = 512 bytes; 011b = 1024 bytes
        .CTL_MAX_PAYLOAD_SIZE      (ctl_max_payload_size),
        // BAR aperture value (Intel FPGA only). Defines the size of the address
        // space of BAR in the number of usable address bits.
        .CTL_BAR_APERTURE          (6'd26),

        // =====================================================================
        // MI32 interface (master)
        // =====================================================================

        // MI bus: PCIe function number that generated the current MI request
        .MI_FUNCTION               (mi_function),
        // MI bus: data from master to slave (write data)
        .MI_DWR                    (config_mi.DWR),
        // MI bus: slave address
        .MI_ADDR                   (config_mi.ADDR),
        // MI bus: byte enable
        .MI_BE                     (config_mi.BE),
        // MI bus: read request
        .MI_RD                     (config_mi.RD),
        // MI bus: write request
        .MI_WR                     (config_mi.WR),
        // MI bus: ready of slave module
        .MI_ARDY                   (config_mi.ARDY),
        // MI bus: data from slave to master (read data)
        .MI_DRD                    (config_mi.DRD),
        // MI bus: valid of MI_DRD data signal
        .MI_DRDY                   (config_mi.DRDY),

        // =====================================================================
        // MFB Completer Request (CQ) Interface
        // =====================================================================

        .CQ_MFB_DATA          (mfb_cq.DATA),
        .CQ_MFB_META          (mfb_cq.META),
        .CQ_MFB_SOF_POS       (cq_sof_pos),
        .CQ_MFB_EOF_POS       (mfb_cq.EOF_POS),
        .CQ_MFB_SOF           (mfb_cq.SOF),
        .CQ_MFB_EOF           (mfb_cq.EOF),
        .CQ_MFB_SRC_RDY       (mfb_cq.SRC_RDY),
        .CQ_MFB_DST_RDY       (mfb_cq.DST_RDY),

        // =====================================================================
        // MFB Completer Completion (CC) Interface
        // =====================================================================

        .CC_MFB_DATA          (mfb_cc.DATA),
        .CC_MFB_META          (mfb_cc.META),
        .CC_MFB_SOF_POS       (cc_sof_pos),
        .CC_MFB_EOF_POS       (mfb_cc.EOF_POS),
        .CC_MFB_SOF           (mfb_cc.SOF),
        .CC_MFB_EOF           (mfb_cc.EOF),
        .CC_MFB_SRC_RDY       (mfb_cc.SRC_RDY),
        .CC_MFB_DST_RDY       (mfb_cc.DST_RDY)
    );


endmodule
