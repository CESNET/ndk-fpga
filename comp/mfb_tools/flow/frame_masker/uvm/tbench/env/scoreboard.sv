// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kondys <kondys@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class scoreboard #(MFB_REGIONS, MFB_ITEM_WIDTH, MFB_META_WIDTH) extends uvm_scoreboard;
    `uvm_component_param_utils(frame_masker::scoreboard #(MFB_REGIONS, MFB_ITEM_WIDTH, MFB_META_WIDTH))

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) data_dut;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH))       meta_dut;

    protected model #(MFB_REGIONS, MFB_ITEM_WIDTH, MFB_META_WIDTH) m_model;

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) m_data_subscriber;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH))       m_meta_subscriber;

    protected uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) data_cmp;
    protected uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH))       meta_cmp;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        data_dut = new("data_dut", this);
        meta_dut = new("meta_dut", this);

        m_data_subscriber = new("m_data_subscriber", this);
        m_meta_subscriber = new("m_meta_subscriber", this);

    endfunction

    function int unsigned success();
        int unsigned ret = 1;
        ret &= data_cmp.success();
        ret &= meta_cmp.success();
        return ret;
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= data_cmp.used();
        ret |= meta_cmp.used();
        ret |= m_model.input_data.used();
        ret |= m_model.input_meta.used();
        return ret;
    endfunction


    function void build_phase(uvm_phase phase);
        m_model = model #(MFB_REGIONS, MFB_ITEM_WIDTH, MFB_META_WIDTH)::type_id::create("m_model", this);

        data_cmp = uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH))::type_id::create("data_cmp", this);
        meta_cmp = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH))      ::type_id::create("meta_cmp", this);

    endfunction

    function void connect_phase(uvm_phase phase);

        // connects the input data (from the Subscriber - connection in Env) to the input of the Model
        m_data_subscriber.connect(m_model.input_data.analysis_export);
        m_meta_subscriber.connect(m_model.input_meta.analysis_export);
        // and then from the Model to the Comparator
        m_model.out_data.connect(data_cmp.analysis_imp_model);
        m_model.out_meta.connect(meta_cmp.analysis_imp_model);

        // connects the data and metadata from the DUT to the Comparator
        data_dut.connect(data_cmp.analysis_imp_dut);
        meta_dut.connect(meta_cmp.analysis_imp_dut);

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
