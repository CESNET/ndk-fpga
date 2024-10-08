// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Mikuláš Brázda <xbrazd21@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class scoreboard#(ITEM_WIDTH, META_WIDTH) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_mfb_fifox::scoreboard#(ITEM_WIDTH, META_WIDTH))

    int unsigned errors = 0;
    int unsigned compared = 0;

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))    input_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(META_WIDTH)) input_meta;

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))    out_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(META_WIDTH)) out_meta;

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))  dut_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(META_WIDTH)) dut_meta;

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))  model_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(META_WIDTH)) model_meta;

    model#(ITEM_WIDTH, META_WIDTH) m_model;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        input_data = new("input_data", this);
        input_meta = new("input_meta", this);
        out_data   = new("out_data", this);
        out_meta   = new("out_meta", this);
        dut_data   = new("dut_data", this);
        dut_meta   = new("dut_meta", this);
        model_data = new("model_data", this);
        model_meta   = new("model_meta", this);

    endfunction

    function void build_phase(uvm_phase phase);
        m_model = model#(ITEM_WIDTH, META_WIDTH)::type_id::create("m_model", this);
    endfunction

    function void connect_phase(uvm_phase phase);

        // connects input data to the input of the model
        input_data.connect(m_model.input_data.analysis_export);
        input_meta.connect(m_model.input_meta.analysis_export);

        // processed data from the output of the model connected to the analysis fifo
        m_model.out_data.connect(model_data.analysis_export);
        m_model.out_meta.connect(model_meta.analysis_export);

        // connects the data from the DUT to the analysis fifo
        out_data.connect(dut_data.analysis_export);
        out_meta.connect(dut_meta.analysis_export);
    endfunction

    task run_phase(uvm_phase phase);

        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) tr_dut;
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) tr_model;
        uvm_logic_vector::sequence_item#(META_WIDTH) tr_dut_meta;
        uvm_logic_vector::sequence_item#(META_WIDTH) tr_model_meta;

        forever begin
            model_data.get(tr_model);
            model_meta.get(tr_model_meta);
            dut_data.get(tr_dut);
            dut_meta.get(tr_dut_meta);

            compared++;

            if (tr_model.compare(tr_dut) == 0) begin
                string msg;

                msg = $sformatf( "\n\tPacket comparison failed! \n\tModel packet:\n%s\n\tDUT packet:\n%s", tr_model.convert2string(), tr_dut.convert2string());
                `uvm_error(this.get_full_name(), msg);
                errors++;
            end

            if (tr_model_meta.compare(tr_dut_meta) == 0) begin
                string msg;

                msg = $sformatf( "\n\tMetadata comparison failed! \n\tModel metadata:\n%s\n\tDUT metadata:\n%s", tr_model_meta.convert2string(), tr_dut_meta.convert2string());
                `uvm_error(this.get_full_name(), msg);
                errors++;
            end
        end

    endtask

    function void report_phase(uvm_phase phase);
        string str = "";

        str = $sformatf( "\n\tCompared packets: %0d", compared);
        if (errors == 0) begin
            `uvm_info(get_type_name(), {str, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {str, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------"}, UVM_NONE)
        end


    endfunction

endclass
