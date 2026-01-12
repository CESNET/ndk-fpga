//-- sequence.sv: Convert PCIE transaction to mfb and mvb Trasnactions
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet>
//-- SPDX-License-Identifier: BSD-3-Clause

class sequence_base_mfb_rq #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    meta_position_t META_TYPE
) extends uvm_common::sequence_base#(
    uvm_mfb::config_sequence,
    uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, 32, (META_TYPE !=  MFB_META_NONE) ? meta_width_get(MFB_RQ) : 0)
);
    `uvm_object_param_utils(uvm_pcie_mfb::sequence_base_mfb_rq #(REGIONS, REGION_SIZE, BLOCK_SIZE, META_TYPE));

    int unsigned transactions_min = 10;
    int unsigned transactions_max = 300;
    rand int unsigned transactions;

    constraint c_transactions {
        transactions inside {[transactions_min:transactions_max]};
    }

    function new(string name = "uvm_pcie_mfb::sequence_simple");
        super.new(name);
    endfunction


    task body;
        for(int unsigned it = 0; it < transactions; it++) begin
            `uvm_error(m_sequencer.get_full_name(), $sformatf("\nNOT IMPLEMENTED"));
        end
    endtask
endclass



/////////////////////////////////////////////////////////////////////////
// SEQUENCE LIBRARY UP
class sequence_lib_mfb_rq #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    meta_position_t META_TYPE
) extends uvm_common::sequence_library#(
    uvm_mfb::config_sequence,
    uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, 32, (META_TYPE !=  MFB_META_NONE) ? meta_width_get(MFB_RQ) : 0)
);

    `uvm_object_param_utils(uvm_pcie_mfb::sequence_lib_mfb_rq#(REGIONS, REGION_SIZE, BLOCK_SIZE, META_TYPE))
    `uvm_sequence_library_utils(uvm_pcie_mfb::sequence_lib_mfb_rq#(REGIONS, REGION_SIZE, BLOCK_SIZE, META_TYPE))

    function new(string name = "sequence_lib_rx");
      super.new(name);
      init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(uvm_mfb::config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(uvm_pcie_mfb::sequence_base_mfb_rq #(REGIONS, REGION_SIZE, BLOCK_SIZE, META_TYPE)::get_type());
    endfunction
endclass



