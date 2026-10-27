//-- property.sv: Properties for mfb bus
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`include "uvm_macros.svh"
import uvm_pkg::*;

module ptc_property #(DMA_MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, MFB_UP_ITEM_WIDTH,
                      DMA_MVB_UP_ITEMS, MFB_UP_REGIONS, PCIE_UP_META_WIDTH,
                      MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH,
                      PCIE_DOWN_META_WIDTH, DMA_MFB_DOWN_REGIONS, DMA_MVB_DOWN_ITEMS, DMA_PORTS, DEVICE,
                      ENDPOINT_TYPE)
    (
        input RESET,
        input RESET_DMA,
        mfb_if up_mfb_vif [DMA_PORTS],
        mfb_if rq_mfb_vif,
        mfb_if down_mfb_vif [DMA_PORTS],
        mfb_if rc_mfb_vif,
        mvb_if up_mvb_vif [DMA_PORTS],
        mvb_if rq_mvb_vif,
        mvb_if down_mvb_vif [DMA_PORTS],
        axi_if rq_axi_vif,
        axi_if rc_axi_vif
    );


    localparam RQ_AXI_ITEMS = MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE;
    localparam RC_AXI_ITEMS = MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE;

    string module_name = "";
    logic START = 1'b1;

    ///////////////////
    // Start check properties after first clock
    initial begin
        $sformat(module_name, "%m");
        @(posedge rq_mvb_vif.CLK)
        #(10ps)
        START = 1'b0;
    end

    for (genvar dma_port = 0; dma_port < DMA_PORTS; dma_port++) begin : gen_dma_port
        mfb_property #(
            .REGIONS      (DMA_MFB_UP_REGIONS),
            .REGION_SIZE  (MFB_UP_REG_SIZE),
            .BLOCK_SIZE   (MFB_UP_BLOCK_SIZE),
            .ITEM_WIDTH   (MFB_UP_ITEM_WIDTH),
            .META_WIDTH   (0)
        )
        up_mfb_prop (
            .RESET (RESET_DMA),
            .vif   (up_mfb_vif[dma_port])
        );

        mvb_property #(
            .ITEMS      (DMA_MVB_UP_ITEMS),
            .ITEM_WIDTH (sv_dma_bus_pack::DMA_UPHDR_WIDTH)
        )
        up_mvb_prop (
            .RESET (RESET_DMA),
            .vif   (up_mvb_vif[dma_port])
        );

        mfb_property #(
            .REGIONS      (DMA_MFB_DOWN_REGIONS),
            .REGION_SIZE  (MFB_DOWN_REG_SIZE),
            .BLOCK_SIZE   (MFB_DOWN_BLOCK_SIZE),
            .ITEM_WIDTH   (MFB_DOWN_ITEM_WIDTH),
            .META_WIDTH   (sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)
        )
        down_mfb_prop (
            .RESET (RESET_DMA),
            .vif   (down_mfb_vif[dma_port])
        );

        mvb_property #(
            .ITEMS      (DMA_MVB_DOWN_ITEMS),
            .ITEM_WIDTH (sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)
        )
        down_mvb_prop (
            .RESET (RESET_DMA),
            .vif   (down_mvb_vif[dma_port])
        );
    end


    generate
        if (DEVICE == "AGILEX" || DEVICE == "STRATIX10") begin : gen_DEVICE_AGILEX_DEVICE_STRATIX10
            mvb_property #(
                .ITEMS      (MFB_UP_REGIONS),
                .ITEM_WIDTH (PCIE_UP_META_WIDTH)
            )
            rq_mvb_prop (
                .RESET (RESET),
                .vif   (rq_mvb_vif)
            );

            mfb_property #(
                .REGIONS      (MFB_DOWN_REGIONS),
                .REGION_SIZE  (MFB_DOWN_REG_SIZE),
                .BLOCK_SIZE   (MFB_DOWN_BLOCK_SIZE),
                .ITEM_WIDTH   (MFB_DOWN_ITEM_WIDTH),
                .META_WIDTH   (0)
            )
            rc_mfb_prop (
                .RESET (RESET),
                .vif   (rc_mfb_vif)
            );

            mfb_property #(
                .REGIONS      (MFB_UP_REGIONS),
                .REGION_SIZE  (MFB_UP_REG_SIZE),
                .BLOCK_SIZE   (MFB_UP_BLOCK_SIZE),
                .ITEM_WIDTH   (MFB_UP_ITEM_WIDTH),
                .META_WIDTH   (0)
            )
            rq_mfb_prop (
                .RESET (RESET),
                .vif   (rq_mfb_vif)
            );
        end else begin : gen_line_123
            axi_property #(
                .ITEMS      (RQ_AXI_ITEMS),
                .ITEM_WIDTH (32),
                .TUSER_WIDTH(uvm_pcie_axi::tuser_width_get(RQ_AXI_ITEMS, uvm_pcie_axi::AXI_RQ))
            ) AXI_RQ (
                .RESET (RESET),
                .vif   (rq_axi_vif)
            );
            axi_property  #(
                .ITEMS      (RC_AXI_ITEMS),
                .ITEM_WIDTH (32),
                .TUSER_WIDTH(uvm_pcie_axi::tuser_width_get(RC_AXI_ITEMS, uvm_pcie_axi::AXI_RC))
            ) AXI_RC (
                .RESET (RESET_DMA),
                .vif   (rc_axi_vif)
            );
        end
    endgenerate

    // This property check if MFB SOF is same as MVB VLD
    property sof_with_vld(int unsigned region);
        @(posedge rq_mvb_vif.CLK)
        disable iff(RESET || START)
        $rose(rq_mfb_vif.SOF[region]) |-> (rq_mfb_vif.SOF[region] == rq_mvb_vif.VLD[region]);
    endproperty

    for(genvar it = 0; it < MFB_UP_REGIONS; it++) begin : gen_it
        assert property (sof_with_vld(it))
            else begin
                `uvm_error(module_name, "\n\tMVB interface: MFB SOF is not same as MVB VLD.");
            end
    end

    // =========================================================================
    // R-Tile TX interface rules
    // =========================================================================
    // One region of the RQ MFB bus is one segment of the R-Tile TX interface.
    // A TLP can start only in segments st0 and st2 (4 regions) or st0 and st1
    // (2 regions). A TLP starts in a higher segment only when the previous TLP
    // ends in a lower segment. See the R-Tile Avalon-ST IP for PCIe User Guide
    // (683501), Tables 59 and 60.
    generate
        if (DEVICE == "AGILEX" && ENDPOINT_TYPE == "R_TILE") begin : gen_rtile_tx_rules
            localparam int unsigned SOF_STEP = (MFB_UP_REGIONS > 1) ? MFB_UP_REGIONS/2 : 1;

            for (genvar r = 1; r < MFB_UP_REGIONS; r++) begin : gen_rtile_region
                if ((r % SOF_STEP) != 0) begin : gen_no_sof
                    property rq_no_sof;
                        @(posedge rq_mfb_vif.CLK)
                        disable iff(RESET || START)
                        (rq_mfb_vif.SRC_RDY && rq_mfb_vif.DST_RDY) |-> (rq_mfb_vif.SOF[r] === 1'b0);
                    endproperty

                    assert property (rq_no_sof)
                        else begin
                            `uvm_error(module_name, $sformatf(
                                "\n\tRQ MFB interface: SOF in region %0d, R-Tile does not allow a TLP start here.", r));
                        end
                end else begin : gen_sof_after_eof
                    property rq_sof_after_eof;
                        @(posedge rq_mfb_vif.CLK)
                        disable iff(RESET || START)
                        (rq_mfb_vif.SRC_RDY && rq_mfb_vif.DST_RDY && rq_mfb_vif.SOF[r]) |-> (|rq_mfb_vif.EOF[r-1:0]);
                    endproperty

                    assert property (rq_sof_after_eof)
                        else begin
                            `uvm_error(module_name, $sformatf(
                                "\n\tRQ MFB interface: SOF in region %0d without EOF in a lower region.", r));
                        end

                    // A TLP that starts in this region ends in the same word.
                    property rq_eof_in_word;
                        @(posedge rq_mfb_vif.CLK)
                        disable iff(RESET || START)
                        (rq_mfb_vif.SRC_RDY && rq_mfb_vif.DST_RDY && rq_mfb_vif.SOF[r])
                            |-> (|rq_mfb_vif.EOF[MFB_UP_REGIONS-1:r]);
                    endproperty

                    assert property (rq_eof_in_word)
                        else begin
                            `uvm_error(module_name, $sformatf(
                                "\n\tRQ MFB interface: TLP that starts in region %0d does not end in the word.", r));
                        end
                end
            end

            // A TLP has no cycle with SRC_RDY low and DST_RDY high between SOF and EOF.
            // The R-Tile TX interface does not allow VALID low inside a TLP.
            logic rq_tlp_open = 1'b0;

            always @(posedge rq_mfb_vif.CLK) begin
                if (RESET !== 1'b0) begin
                    rq_tlp_open = 1'b0;
                end else if (rq_mfb_vif.DST_RDY === 1'b1) begin
                    if (rq_mfb_vif.SRC_RDY !== 1'b1) begin
                        if (rq_tlp_open) begin
                            `uvm_error(module_name, "\n\tRQ MFB interface: SRC_RDY is low inside a TLP.");
                        end
                    end else begin
                        for (int unsigned r = 0; r < MFB_UP_REGIONS; r++) begin
                            if (rq_mfb_vif.SOF[r] === 1'b1) begin
                                rq_tlp_open = 1'b1;
                            end
                            if (rq_mfb_vif.EOF[r] === 1'b1) begin
                                rq_tlp_open = 1'b0;
                            end
                        end
                    end
                end
            end

            // Number of RQ MFB words with the given number of SOF
            int unsigned sof_per_word[MFB_UP_REGIONS+1];

            always @(posedge rq_mfb_vif.CLK) begin
                if (RESET !== 1'b1 && rq_mfb_vif.SRC_RDY === 1'b1 && rq_mfb_vif.DST_RDY === 1'b1) begin
                    sof_per_word[$countones(rq_mfb_vif.SOF)]++;
                end
            end

            final begin
                for (int unsigned i = 0; i <= MFB_UP_REGIONS; i++) begin
                    $display("RQ MFB STATS: words with %0d SOF: %0d", i, sof_per_word[i]);
                end
            end
        end
    endgenerate

endmodule
