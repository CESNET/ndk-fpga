// meta_splitter.sv: Splits input into output extension and metadata
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class meta_splitter #(
    int unsigned USERMETA_WIDTH,
    int unsigned RX_MVB_ITEM_WIDTH
) extends uvm_subscriber #(uvm_logic_vector::sequence_item #(RX_MVB_ITEM_WIDTH));
    `uvm_component_param_utils(uvm_mfb_frame_extender::meta_splitter #(USERMETA_WIDTH, RX_MVB_ITEM_WIDTH))

    // Outputs
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(USERMETA_WIDTH))                   analysis_port_meta;
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(RX_MVB_ITEM_WIDTH-USERMETA_WIDTH)) analysis_port_extension;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        analysis_port_meta      = new("analysis_port_meta", this);
        analysis_port_extension = new("analysis_port_extension", this);
    endfunction

    function void write(uvm_logic_vector::sequence_item #(RX_MVB_ITEM_WIDTH) t);
        // verilog_lint: waive line-length
        uvm_logic_vector::sequence_item #(RX_MVB_ITEM_WIDTH-USERMETA_WIDTH) out_extension_item = uvm_logic_vector::sequence_item #(RX_MVB_ITEM_WIDTH-USERMETA_WIDTH)::type_id::create("out_extension_item");
        // verilog_lint: waive line-length
        uvm_logic_vector::sequence_item #(USERMETA_WIDTH)                   out_meta_item      = uvm_logic_vector::sequence_item #(USERMETA_WIDTH)                  ::type_id::create("out_meta_item");

        out_extension_item.data = t.data[RX_MVB_ITEM_WIDTH-USERMETA_WIDTH-1 -: RX_MVB_ITEM_WIDTH-USERMETA_WIDTH];
        out_meta_item     .data = t.data[RX_MVB_ITEM_WIDTH               -1 -: USERMETA_WIDTH];

        analysis_port_extension.write(out_extension_item);
        analysis_port_meta     .write(out_meta_item);
    endfunction

endclass
