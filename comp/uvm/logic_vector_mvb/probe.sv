// probe_dma_read_tag.sv: Bound probe interface for DMA read upstream MVB
// Copyright (C) 2026 CESNET z. s. p. o.

// SPDX-License-Identifier: BSD-3-Clause

interface logic_vector_mvb_probe_if #(
    int unsigned REGIONS,
    int unsigned DATA_WIDTH
) (
    input logic [REGIONS*DATA_WIDTH-1:0] data,
    input logic [REGIONS-1:0]           vld,
    input logic                         src_rdy,
    input logic                         dst_rdy,
    input logic                         CLK
);
    mvb_if #(REGIONS, DATA_WIDTH) inf (CLK);

    assign inf.DATA    = data;
    assign inf.VLD     = vld;
    assign inf.SRC_RDY = src_rdy;
    assign inf.DST_RDY = dst_rdy;

    `include "ndk_macros.svh"
    import uvm_pkg::*;
    localparam string PATH = $sformatf("%m");

    class dma_probe #(
        int unsigned REGIONS,
        int unsigned DATA_WIDTH
    ) extends uvm_env;
        `ndk_component_param_utils(
            dma_probe#(REGIONS, DATA_WIDTH),
            $sformatf("dma_probe#(%0d,%0d)", REGIONS, DATA_WIDTH)
        )

        protected uvm_logic_vector_mvb::env_rx#(REGIONS, DATA_WIDTH) m_mvb;
        protected uvm_analysis_export#(uvm_logic_vector::sequence_item#(DATA_WIDTH)) analysis_export;

        function new(string name, uvm_component parent);
            super.new(name, parent);
        endfunction

        function void build_phase (uvm_phase phase);
            uvm_logic_vector_mvb::config_item cfg;

            cfg = new();
            cfg.active = UVM_PASSIVE;
            cfg.interface_name = {PATH, ".vif_dma_read_tag_probe"};
            uvm_config_db#(uvm_logic_vector_mvb::config_item)::set(this, "m_mvb", "m_config", cfg);
            m_mvb = uvm_logic_vector_mvb::env_rx#(REGIONS, DATA_WIDTH)::type_id::create("m_mvb", this);

            analysis_export = new("analysis_export", this);
            uvm_config_db#(
                uvm_analysis_export#(uvm_logic_vector::sequence_item#(DATA_WIDTH))
            )::set(null, PATH, "dma_analysis_port", this.analysis_export);
        endfunction

        function void connect_phase (uvm_phase phase);
            m_mvb.analysis_port.connect(analysis_export);
        endfunction
    endclass

    dma_probe#(REGIONS, DATA_WIDTH) probe;

    initial begin
        uvm_config_db#(virtual mvb_if #(REGIONS, DATA_WIDTH))::set(null, "", {PATH, ".vif_dma_read_tag_probe"}, inf);
        probe = dma_probe#(REGIONS, DATA_WIDTH)::type_id::create({PATH, "probe"}, null);
    end
endinterface
