// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class scoreboard#(ITEM_WIDTH) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_ptc_pcie_axi2mfb::scoreboard#(ITEM_WIDTH))

    uvm_common::subscriber #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)) input_data;
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH))    out_data;

    uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) data_cmp;

    uvm_pcie_mfb2avst::model#(ITEM_WIDTH, 0) m_model;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        out_data   = new("out_data", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= data_cmp.used();
        ret |= data_cmp.errors != 0;
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        m_model = uvm_pcie_mfb2avst::model#(ITEM_WIDTH, 0)::type_id::create("m_model", this);

        input_data = uvm_common::subscriber #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))::type_id::create("input_data", this);

        data_cmp   = uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))::type_id::create("data_cmp", this);
    endfunction

    function void connect_phase(uvm_phase phase);

        // connects input data to the input of the model
        input_data.port.connect(m_model.data_in.analysis_export);

        // processed data from the output of the model connected to the analysis fifo
        m_model.data_out.connect(data_cmp.analysis_imp_model);
        // connects the data from the DUT to the analysis fifo
        out_data.connect(data_cmp.analysis_imp_dut);

    endfunction

    virtual function void report_phase(uvm_phase phase);
        string msg = "\n";
        msg = {msg, $sformatf("\tCompared/errors: %0d/%0d\n",  data_cmp.compared, data_cmp.errors)};

        if (this.used() == 0) begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------", msg), UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------", msg), UVM_NONE)
        end

    endfunction

endclass
