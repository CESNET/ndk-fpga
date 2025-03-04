// meta_splitter.sv: Splits input into output length and metadata
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class meta_splitter #(int unsigned META_WIDTH, int unsigned LEN_WIDTH) extends uvm_subscriber #(uvm_logic_vector::sequence_item #(META_WIDTH+1+LEN_WIDTH));
    `uvm_component_param_utils(uvm_mfb_frame_trimmer::meta_splitter #(META_WIDTH, LEN_WIDTH))

    // ------------ //
    // Output ports //
    // ------------ //

    uvm_analysis_port #(uvm_logic_vector::sequence_item #(1+LEN_WIDTH)) analysis_port_len;
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(META_WIDTH))  analysis_port_meta;

    function new(string name = "meta_splitter", uvm_component parent = null);
        super.new(name, parent);

        analysis_port_len  = new("analysis_port_len", this);
        analysis_port_meta = new("analysis_port_meta", this);
    endfunction

    function void write(uvm_logic_vector::sequence_item #(META_WIDTH+1+LEN_WIDTH) t);
        uvm_logic_vector::sequence_item #(1+LEN_WIDTH) out_len_item  = uvm_logic_vector::sequence_item #(1+LEN_WIDTH)::type_id::create("out_len_item");
        uvm_logic_vector::sequence_item #(META_WIDTH)  out_meta_item = uvm_logic_vector::sequence_item #(META_WIDTH) ::type_id::create("out_meta_item");

        out_len_item.data  = t.data[1+LEN_WIDTH           -1 -: 1+LEN_WIDTH];
        out_meta_item.data = t.data[META_WIDTH+1+LEN_WIDTH-1 -: META_WIDTH];

        analysis_port_len .write(out_len_item);
        analysis_port_meta.write(out_meta_item);
    endfunction

endclass
