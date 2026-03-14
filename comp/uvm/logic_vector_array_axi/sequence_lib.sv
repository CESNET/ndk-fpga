//-- sequence.sv: Mfb sequence
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

/////////////////////////////////////////////////////////////////////////
// SEQUENCE LIBRARY RX

class sequence_lib_rx #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_common::sequence_library#(config_sequence, uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, 0));
  `uvm_object_param_utils(uvm_logic_vector_array_axi::sequence_lib_rx#(ITEMS, ITEM_WIDTH))
  `uvm_sequence_library_utils(uvm_logic_vector_array_axi::sequence_lib_rx#(ITEMS, ITEM_WIDTH))

  function new(string name = "sequence_lib_rx");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(uvm_logic_vector_array_axi::sequence_rx#(ITEMS, ITEM_WIDTH)::get_type());
    endfunction
endclass


