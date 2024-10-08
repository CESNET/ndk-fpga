// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(META_WIDTH, MVB_DATA_WIDTH, MFB_ITEM_WIDTH, OFFSET_WIDTH, LENGTH_WIDTH, VERBOSITY, MFB_META_WIDTH) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_checksum_calculator::scoreboard #(META_WIDTH, MVB_DATA_WIDTH, MFB_ITEM_WIDTH, OFFSET_WIDTH, LENGTH_WIDTH, VERBOSITY, MFB_META_WIDTH))

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH))         input_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(META_WIDTH))                   input_meta;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(MVB_DATA_WIDTH+1+MFB_META_WIDTH)) dut_out_mvb;

    uvm_checksum_calculator::chsum_calc_cmp #(MVB_DATA_WIDTH, MFB_META_WIDTH)         data_cmp;

    model #(META_WIDTH, MVB_DATA_WIDTH, MFB_ITEM_WIDTH, OFFSET_WIDTH, LENGTH_WIDTH, VERBOSITY, MFB_META_WIDTH) m_model;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        dut_out_mvb        = new("dut_out_mvb", this);
        input_data = new("input_data", this);
        input_meta = new("input_meta", this);
    endfunction

    function int unsigned success();
        int unsigned ret = 1;
        ret &= data_cmp.success();
        return ret;
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= data_cmp.used();
        return ret;
    endfunction


    function void build_phase(uvm_phase phase);
        m_model    = model#(META_WIDTH, MVB_DATA_WIDTH, MFB_ITEM_WIDTH, OFFSET_WIDTH, LENGTH_WIDTH, VERBOSITY, MFB_META_WIDTH)::type_id::create("m_model", this);

        data_cmp = uvm_checksum_calculator::chsum_calc_cmp #(MVB_DATA_WIDTH, MFB_META_WIDTH)::type_id::create("data_cmp", this);
        data_cmp.model_tr_timeout_set(1ms);

    endfunction

    function void connect_phase(uvm_phase phase);
        input_data.connect(m_model.input_data.analysis_export);
        input_meta.connect(m_model.input_meta.analysis_export);

        m_model.out_checksum.connect(data_cmp.analysis_imp_model);
        dut_out_mvb.connect(data_cmp.analysis_imp_dut);

    endfunction

    function void report_phase(uvm_phase phase);
        string msg = "\n";

        if (this.success() && this.used() == 0) begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAILED       ----\n\t---------------------------------------"}, UVM_NONE)
        end

    endfunction

endclass
