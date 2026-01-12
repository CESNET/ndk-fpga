
//-- sequence.sv: Convert PCIE transaction to axi Trasnactions
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet>
//-- SPDX-License-Identifier: BSD-3-Clause



class sequence_base_cc #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_common::sequence_base#(
    config_sequence,
    uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, tuser_width_get(ITEMS, AXI_CC))
);

    `uvm_object_param_utils(uvm_pcie_axi::sequence_base_cc #(ITEMS, ITEM_WIDTH));

    int unsigned transactions_min = 10;
    int unsigned transactions_max = 300;
    rand int unsigned transactions;

    constraint c_transactions {
        transactions inside {[transactions_min:transactions_max]};
    }

    function new(string name = "uvm_pcie_axi::sequence_simple");
        super.new(name);
    endfunction


    task body;
        for(int unsigned it = 0; it < transactions; it++) begin
            uvm_pcie::header hdr;

            `uvm_error(m_sequencer.get_full_name(), $sformatf("\nSEND TR%s", hdr.convert2string()));
        end
    endtask
endclass



/////////////////////////////////////////////////////////////////////////
// SEQUENCE LIBRARY RX

class sequence_lib_cc #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_common::sequence_library#(
    config_sequence,
    uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, tuser_width_get(ITEMS, AXI_CC))
);

  `uvm_object_param_utils(uvm_pcie_axi::sequence_lib_cc#(ITEMS, ITEM_WIDTH))
  `uvm_sequence_library_utils(uvm_pcie_axi::sequence_lib_cc#(ITEMS, ITEM_WIDTH))

  function new(string name = "sequence_lib_rx");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(uvm_pcie_axi::sequence_base_cc #(ITEMS, ITEM_WIDTH)::get_type());
    endfunction

    task body();
        `uvm_fatal(m_sequencer.get_full_name(), $sformatf("\n\tRQ seqeunce Is not Implemented"));
    endtask
endclass

