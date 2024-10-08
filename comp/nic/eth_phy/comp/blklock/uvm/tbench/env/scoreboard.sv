/*
 * file       : scoreboard.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM Scoreboard for Block Lock
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

class mvb_converter extends uvm_subscriber#(uvm_mvb::sequence_item #(1, 2));
    `uvm_component_utils(uvm_blklock::mvb_converter)

    uvm_analysis_port #(uvm_logic_vector::sequence_item#(2)) analysis_port;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        analysis_port = new("analysis port", this);
    endfunction

    function void write(uvm_mvb::sequence_item #(1, 2) t);
        uvm_logic_vector::sequence_item#(2) tr_out;

        tr_out = uvm_logic_vector::sequence_item#(2)::type_id::create("tr_out", this);
        tr_out.data = t.data[0];
        analysis_port.write(tr_out);
    endfunction
endclass


class scoreboard #(SH_CNT_MAX, SH_INVALID_CNT_MAX, SLIP_WAIT_TIME) extends uvm_scoreboard;

    `uvm_component_param_utils(uvm_blklock::scoreboard#(SH_CNT_MAX, SH_INVALID_CNT_MAX, SLIP_WAIT_TIME))
    uvm_analysis_export #(uvm_mvb::sequence_item #(1, 2)) analysis_imp_mvb_rx;
    uvm_analysis_export #(uvm_mvb::sequence_item #(1, 2)) analysis_imp_mvb_tx;
    model #(SH_CNT_MAX, SH_INVALID_CNT_MAX, SLIP_WAIT_TIME) m_model ;

    uvm_analysis_export #(uvm_reset::sequence_item) analysis_imp_reset;

    local uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(2)) rx_fifo;
    local uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(2)) tx_fifo;

    local mvb_converter mvb_converter_tx;

    local int unsigned compared = 0;
    local int unsigned errors   = 0;

    string msg;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        analysis_imp_mvb_rx = new("analysis_imp_mvb_rx", this);
        analysis_imp_mvb_tx = new("analysis_imp_mvb_tx", this);

        analysis_imp_reset = new("analysis_imp_reset", this);

        rx_fifo = new("rx_fifo", this);
        tx_fifo = new("tx_fifo", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (rx_fifo.used() != 0);
        ret |= (tx_fifo.used() != 0);
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        m_model = model #(SH_CNT_MAX, SH_INVALID_CNT_MAX, SLIP_WAIT_TIME)::type_id::create("m_model", this);
        mvb_converter_tx = mvb_converter::type_id::create("mvb_converter_tx", this);
    endfunction


    function void connect_phase(uvm_phase phase);
        // Connect stimulus from agent to model
        analysis_imp_mvb_rx.connect(m_model.input_data.analysis_export);
        // Connect model output to FIFO
        m_model.output_data.connect(rx_fifo.analysis_export);

        // Connect RESET signal to model
        analysis_imp_reset.connect(m_model.reset.analysis_export);

        // Connect output from  to scoreboard and convert it to logic_vector
        analysis_imp_mvb_tx.connect(mvb_converter_tx.analysis_export);
        mvb_converter_tx.analysis_port.connect(tx_fifo.analysis_export);
    endfunction


    task run_phase(uvm_phase phase);
        uvm_logic_vector::sequence_item#(2) tr_model;
        uvm_logic_vector::sequence_item#(2) tr_dut;

        forever begin
            rx_fifo.get(tr_model);
            tx_fifo.get(tr_dut);

            compared++;
            if (tr_model.compare(tr_dut) == 0) begin
                errors++;
                msg = {msg, $sformatf("\n---Transactions does not match---\n\tMODEL Transaction\n%s\n\n\tDUT Transaction\n%s\n",  tr_model.convert2string(), tr_dut.convert2string())};
            end
        end
    endtask

    virtual function void report_phase(uvm_phase phase);
        msg = {msg, $sformatf("\nCompared/errors: %0d/%0d \n",  compared, errors)};
        msg = {msg, $sformatf("Count of items inside fifo: %d \n",  rx_fifo.used())};
        msg = {msg, $sformatf("Errors : %d \n",  errors)};

        if (errors == 0 && this.used() == 0) begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------", msg), UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------", msg), UVM_NONE)
        end

    endfunction

endclass
