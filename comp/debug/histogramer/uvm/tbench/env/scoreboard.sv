//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author: Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

//TODO
`include "../tests/const.sv"

class scoreboard #(
    INPUT_WIDTH,
    BOX_WIDTH,
    BOX_CNT,
    READ_PRIOR,
    CLEAR_BY_READ,
    CLEAR_BY_RST,
    DEVICE,
    REQ_WIDTH,
    RESP_WIDTH,
    ADDR_WIDTH
) extends uvm_scoreboard;

    `uvm_component_utils(uvm_histogramer::scoreboard #(
        INPUT_WIDTH,
        BOX_WIDTH,
        BOX_CNT,
        READ_PRIOR,
        CLEAR_BY_READ,
        CLEAR_BY_RST,
        DEVICE,
        REQ_WIDTH,
        RESP_WIDTH,
        ADDR_WIDTH
    ))
    // Analysis components.
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(REQ_WIDTH))    in_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(RESP_WIDTH))   out_data;

    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(RESP_WIDTH)) dut_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(RESP_WIDTH)) model_data;

    model #(
        INPUT_WIDTH,
        BOX_WIDTH,
        BOX_CNT,
        READ_PRIOR,
        CLEAR_BY_READ,
        CLEAR_BY_RST,
        DEVICE,
        REQ_WIDTH,
        RESP_WIDTH,
        ADDR_WIDTH
    ) m_model;

    string msg = "\n";
    local int unsigned compared_data    = 0;
    local int unsigned errors_data      = 0;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        in_data     = new("in_data",     this);
        out_data    = new("out_data",    this);

        dut_data    = new("dut_data",    this);
        model_data  = new("model_data",  this);
    endfunction

    function void build_phase(uvm_phase phase);
        m_model = model#(
            INPUT_WIDTH,
            BOX_WIDTH,
            BOX_CNT,
            READ_PRIOR,
            CLEAR_BY_READ,
            CLEAR_BY_RST,
            DEVICE,
            REQ_WIDTH,
            RESP_WIDTH,
            ADDR_WIDTH
        )::type_id::create("m_model", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;

        ret |= (dut_data.used()    != 0);
        ret |= (model_data.used()  != 0);
        ret |= (m_model.used()     != 0);

        return ret;
    endfunction

    function void connect_phase(uvm_phase phase);
        in_data.connect(m_model.in_data.analysis_export);
        m_model.out_data.connect(model_data.analysis_export);
        out_data.connect(dut_data.analysis_export);
    endfunction


    task run_phase(uvm_phase phase);
        fork
            compare_data();
        join
    endtask

    function automatic string resp_to_string(logic [RESP_WIDTH - 1 : 0] resp);
        string  res = "";
        logic [BOX_WIDTH - 1 : 0] box;

        box = resp;

        $swrite(res, "Box value = %d\n", box);
        return res;
    endfunction

    task compare_data();
        uvm_logic_vector::sequence_item#(RESP_WIDTH) tr_dut_data;
        uvm_logic_vector::sequence_item#(RESP_WIDTH) tr_model_data;
        forever begin

            model_data.get(tr_model_data);
            dut_data.get(tr_dut_data);
            compared_data++;

            if (tr_model_data.compare(tr_dut_data) == 0) begin
                errors_data++;
                $swrite(msg, "\Output does'nt match\n\tModel:\n%s\n\n\tDUT:\n%s", resp_to_string(tr_model_data.data),
                        resp_to_string(tr_dut_data.data));
                `uvm_fatal(get_type_name(), $sformatf("%s", msg))
            end
        end
    endtask

    virtual function void report_phase(uvm_phase phase);

        $swrite(msg, "%s\n\n--- STATUS ---\n", msg);
        $swrite(msg, "%sData:  Compared/errors: %0d/%0d \n", msg, compared_data,  errors_data);
        $swrite(msg, "%s\n", msg);
        $swrite(msg, "%sCount of items inside dut   data  fifo: %0d \n", msg, dut_data.used());
        $swrite(msg, "%sCount of items inside model data  fifo: %0d \n", msg, model_data.used());
        $swrite(msg, "%sErrors:                                 %0d \n", msg, errors_data);

        if (errors_data == 0 && this.used() == 0) begin
            `uvm_info(
                get_type_name(),
                $sformatf(
                    // verilog_lint: waive line-length
                    "%s\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------",
                    msg), UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), $sformatf(
                      "%s\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------"
                          ,
                      msg
                      ), UVM_NONE)
        end
    endfunction

endclass
