/*
 * file       : scoreboard.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: scoreboard
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class scoreboard extends uvm_scoreboard;
   `uvm_component_utils(uvm_mac_seg_rx::scoreboard)

    localparam LOGIC_WIDTH = 6;
    localparam ITEM_WIDTH = 8;

    //CONNECT DUT
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))                 analysis_export_rx_packet;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(LOGIC_WIDTH)) analysis_export_rx_error;
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))                 analysis_export_tx_packet;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(1))           analysis_export_tx_error;
    //output fifos
    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))       model_fifo_packet;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(1)) model_fifo_error;
    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))       dut_fifo_packet;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(1)) dut_fifo_error;
    //models
    model m_model;
    //statistic

    int unsigned compared;
    int unsigned errors;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);


        analysis_export_rx_packet   = new("analysis_export_rx_packet", this);
        analysis_export_rx_error = new("analysis_export_rx_error", this);
        analysis_export_tx_packet = new("analysis_export_tx_packet", this);
        analysis_export_tx_error  = new("analysis_export_tx_error", this);
        model_fifo_packet = new("model_fifo_packet", this);
        model_fifo_error  = new("model_fifo_error", this);
        dut_fifo_packet   = new("dut_fifo_packet", this);
        dut_fifo_error    = new("dut_fifo_error", this);
        compared   = 0;
    endfunction

    function int unsigned used();
        int unsigned ret;
        ret |= model_fifo_packet.used();
        ret |= model_fifo_error.used();
        ret |= dut_fifo_packet.used();
        ret |= dut_fifo_error.used();
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        m_model = model::type_id::create("m_model", this);
    endfunction

    //recive packet
    function void connect_phase(uvm_phase phase);
        analysis_export_rx_packet.connect(m_model.rx_packet.analysis_export);
        analysis_export_rx_error.connect(m_model.rx_error.analysis_export);
        analysis_export_tx_packet.connect(dut_fifo_packet.analysis_export);
        analysis_export_tx_error.connect(dut_fifo_error.analysis_export);

        m_model.tx_packet.connect(model_fifo_packet.analysis_export);
        m_model.tx_error.connect(model_fifo_error.analysis_export);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) tr_model_packet;
        uvm_logic_vector::sequence_item#(1) tr_model_error;
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) tr_dut_packet;
        uvm_logic_vector::sequence_item#(1) tr_dut_error;

        forever begin
            model_fifo_packet.get(tr_model_packet);
            model_fifo_error.get(tr_model_error);
            dut_fifo_packet.get(tr_dut_packet);
            dut_fifo_error.get(tr_dut_error);

            compared++;
            if (tr_model_packet.compare(tr_dut_packet) == 0 || tr_model_error.compare(tr_dut_error) == 0) begin
                string str = "";
                errors++;
                str = {str, $sformatf("\n\terrors %0d packet %0d",  errors, compared)};
                str = {str, $sformatf("\n\tPACKET FROM DUT\n\t%s\n\tEXPECTED PACKET\n\t%s",  tr_dut_packet.convert2string(), tr_model_packet.convert2string())};
                str = {str, $sformatf("\n\tERROR FROM DUT\n\t%s\n\tEXPECTED ERROR\n\t%s",  tr_dut_error.convert2string(), tr_model_error.convert2string())};
               `uvm_error(this.get_full_name(), str);
            end
            if (compared % 1000 == 0) begin
                $write("Compared packets: %0d\n", compared);
            end
        end
    endtask

    //report
    virtual function void report_phase(uvm_phase phase);
        string str = "";

        str = $sformatf( "\n\tCompared transaction %d\n\tErrors %d\n\tDUT TX fifo %d\n\tModel TX fifo %d", compared, errors, dut_fifo_packet.used(), model_fifo_packet.used());
        str = {str, $sformatf("\n\tDUT TX fifo error : %d\n\tModel TX fifo error : %d\n",  dut_fifo_error.used(), model_fifo_error.used())};

        if (errors == 0 && dut_fifo_packet.used() == 0 && model_fifo_packet.used() == 0 && dut_fifo_error.used() == 0 && model_fifo_error.used() == 0) begin
            `uvm_info(get_type_name(), {str, "\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {str, "\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------"}, UVM_NONE)
        end
    endfunction
endclass
