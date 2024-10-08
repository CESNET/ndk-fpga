// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Vladislav Valek <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class scoreboard extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_mfb_to_lbus_adapter::scoreboard)

    int unsigned compared;
    int unsigned error;

    uvm_analysis_export #(uvm_byte_array::sequence_item)    input_data;
    uvm_analysis_export #(uvm_byte_array::sequence_item)    out_data;

    uvm_tlm_analysis_fifo #(uvm_byte_array::sequence_item)  dut_data;
    uvm_tlm_analysis_fifo #(uvm_byte_array::sequence_item)  model_data;

    model m_model;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        input_data = new("input_data", this);
        out_data   = new("out_data", this);
        dut_data   = new("dut_data", this);
        model_data = new("model_data", this);
        compared   = 0;
        error = 0;

    endfunction

    function void build_phase(uvm_phase phase);
        m_model = model::type_id::create("m_model", this);
    endfunction

    function void connect_phase(uvm_phase phase);

        // connects input data to the input of the model
        input_data.connect(m_model.input_data.analysis_export);

        // processed data from the output of the model connected to the analysis fifo
        m_model.out_data.connect(model_data.analysis_export);
        // connects the data from the DUT to the analysis fifo
        out_data.connect(dut_data.analysis_export);

    endfunction

    task run_phase(uvm_phase phase);

        uvm_byte_array::sequence_item tr_dut;
        uvm_byte_array::sequence_item tr_model;

        forever begin

            model_data.get(tr_model);
            dut_data.get(tr_dut);

            compared++;

            if (tr_model.compare(tr_dut) == 0) begin
                string msg;
                error++;
                msg = $sformatf( "\n\tPacket comparison failed! \n\tModel packet:\n%s\n\tDUT packet:\n%s", tr_model.convert2string(), tr_dut.convert2string());
                `uvm_error(this.get_full_name(), msg);
            end
        end

    endtask

    function void report_phase(uvm_phase phase);

        string msg = "";

        msg = {msg, $sformatf("Compared packets: %0d",  compared)};
       if(error == 0 && dut_data.used() == 0 && model_data.used() == 0) begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
       end else begin
             `uvm_info(get_type_name(), {msg, "\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------"}, UVM_NONE)
       end

    endfunction

endclass
