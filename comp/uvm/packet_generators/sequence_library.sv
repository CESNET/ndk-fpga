// sequence_library.sv: Sequence library of packet generating sequences
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_library #(int unsigned ITEM_WIDTH) extends uvm_common::sequence_library #(config_sequence, uvm_logic_vector_array::sequence_item #(ITEM_WIDTH));
    `uvm_object_param_utils(uvm_packet_generators::sequence_library #(ITEM_WIDTH))
    `uvm_sequence_library_utils(uvm_packet_generators::sequence_library #(ITEM_WIDTH))

    function new(string name = "packet_generator_sequence_library");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(config_sequence param_cfg = null);
        super.init_sequence(param_cfg);

        this.add_sequence(sequence_search   #(ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_flowtest #(ITEM_WIDTH)::get_type());
    endfunction

endclass
