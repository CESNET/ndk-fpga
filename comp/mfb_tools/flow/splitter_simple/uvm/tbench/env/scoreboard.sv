//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@censet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class comparer_data #(ITEM_WIDTH, META_WIDTH) extends uvm_common::comparer_base_ordered#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH), uvm_logic_vector_array::sequence_item#(ITEM_WIDTH));
    `uvm_component_param_utils(uvm_splitter_simple::comparer_data #(ITEM_WIDTH, META_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        return tr_model.compare(tr_dut);
    endfunction

endclass

class comparer_meta #(ITEM_WIDTH, META_WIDTH) extends uvm_common::comparer_base_ordered#(uvm_logic_vector::sequence_item #(META_WIDTH), uvm_logic_vector::sequence_item #(META_WIDTH));
    `uvm_component_param_utils(uvm_splitter_simple::comparer_meta #(ITEM_WIDTH, META_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        return tr_model.compare(tr_dut);
    endfunction
endclass


class scoreboard #(ITEM_WIDTH, META_WIDTH, CHANNELS) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_splitter_simple::scoreboard #(ITEM_WIDTH, META_WIDTH, CHANNELS))

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))               input_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #($clog2(CHANNELS) + META_WIDTH)) input_meta;

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))    out_data[CHANNELS];
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(META_WIDTH))         out_meta[CHANNELS];

    typedef scoreboard #(ITEM_WIDTH, META_WIDTH, CHANNELS) this_type;
    uvm_analysis_imp_reset#(uvm_reset::sequence_item, this_type) analysis_imp_reset;

    protected model #(ITEM_WIDTH, META_WIDTH, CHANNELS) m_model;

    //COMPARERS
    protected comparer_data #(ITEM_WIDTH, META_WIDTH) compare_data[CHANNELS];
    protected comparer_meta #(ITEM_WIDTH, META_WIDTH) compare_meta[CHANNELS];

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        input_data = new("input_data", this);
        input_meta = new("input_meta", this);

        for (int unsigned it = 0; it < CHANNELS; it++) begin
            string it_str;
            it_str.itoa(it);

            out_data[it]        = new({"out_data_", it_str}, this);
            out_meta[it]        = new({"out_meta_", it_str}, this);
        end

        analysis_imp_reset = new("analysis_imp_reset", this);
    endfunction

    function void build_phase(uvm_phase phase);
        m_model    = model #(ITEM_WIDTH, META_WIDTH, CHANNELS)::type_id::create("m_model", this);

        for (int it = 0; it < CHANNELS; it++) begin
            string it_string;

            it_string.itoa(it);
            compare_data[it] = comparer_data #(ITEM_WIDTH, META_WIDTH)::type_id::create({"compare_data_", it_string}, this);
            compare_meta[it] = comparer_meta #(ITEM_WIDTH, META_WIDTH)::type_id::create({"compare_meta_", it_string}, this);
        end

    endfunction

    function void connect_phase(uvm_phase phase);
        input_data.connect(m_model.in_data.analysis_export);
        input_meta.connect(m_model.in_meta.analysis_export);

        for (int it = 0; it < CHANNELS; it++) begin
            string i_string;

            m_model.out_data[it].connect(compare_data[it].analysis_imp_model);
            m_model.out_meta[it].connect(compare_meta[it].analysis_imp_model);
            out_data[it].connect(compare_data[it].analysis_imp_dut);
            out_meta[it].connect(compare_meta[it].analysis_imp_dut);
        end
    endfunction

    function int unsigned used();
        int unsigned ret = 0;

        ret |= m_model.used();
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            ret |= compare_data[it].used();
            ret |= compare_meta[it].used();
        end
        return ret;
    endfunction

    function int unsigned success();
        int unsigned ret = 0;

        for (int unsigned it = 0; it < CHANNELS; it++) begin
            ret |= compare_data[it].success();
            ret |= compare_meta[it].success();
        end
        return ret;
    endfunction

    function void write_reset(uvm_reset::sequence_item tr);
        if (tr.reset == 1'b1) begin
            m_model.reset();
            for (int unsigned it = 0; it < CHANNELS; it++) begin
                compare_data[it].flush();
                compare_meta[it].flush();
            end
        end
    endfunction


    function void report_phase(uvm_phase phase);
        string msg = "";

        if (this.success() && this.used() == 0) begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------"}, UVM_NONE)
        end
    endfunction

endclass
