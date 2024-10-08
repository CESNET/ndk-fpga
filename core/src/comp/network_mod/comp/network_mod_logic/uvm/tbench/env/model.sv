// model.sv: Model of implementation
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kondys <xkondy00@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause 

class model_data#(ITEM_WIDTH, META_WIDTH) extends uvm_common::sequence_item;
    `uvm_object_param_utils(net_mod_logic_env::model_data#(ITEM_WIDTH, META_WIDTH))

    uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data;
    uvm_logic_vector::sequence_item#(META_WIDTH) meta;

    function new (string name = "");
        super.new(name);
    endfunction
endclass



class model #(CHANNELS, ITEM_WIDTH, META_WIDTH, HDR_WIDTH) extends uvm_component;
    `uvm_component_param_utils(net_mod_logic_env::model#(CHANNELS, ITEM_WIDTH, META_WIDTH, HDR_WIDTH))

    // TX path
    uvm_tlm_analysis_fifo#(model_data#(ITEM_WIDTH, META_WIDTH))   tx_input;
    uvm_analysis_port#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) tx_output[CHANNELS];

    // RX path - a simple connection of input to output
    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))   rx_input[CHANNELS];
    uvm_tlm_analysis_fifo#(uvm_logic_vector::sequence_item #(1))                 rx_discard[CHANNELS];

    uvm_analysis_port #(model_data#(ITEM_WIDTH, HDR_WIDTH)) rx_output;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        // TX path
        tx_input = new("tx_input", this);
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            string str_it;

            str_it.itoa(it);
            tx_output[it] = new({"tx_output_", str_it}, this);
        end

        // RX path
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            rx_discard[it] = new($sformatf("rx_discard_%0d", it), this);
            rx_input[it]   = new($sformatf("rx_input_%0d", it), this);
        end
        rx_output  = new("rx_output", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            ret |= rx_input[it].used();
            ret |= rx_discard[it].used();
        end
        return (tx_input.used() | ret);
    endfunction


    task tx_run();
        int unsigned tx_channel;
        model_data#(ITEM_WIDTH, META_WIDTH) tr_input;
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) tr_output;
        forever begin
            // TX path
            tx_input.get(tr_input);

            // choose one !
            // tx_channel = tr_tx_input_meta.data[16]; // if CHANNELS == 1
            tr_output = uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)::type_id::create("tr_output", this);
            tr_output.tag   = tr_input.tag;
            tr_output.start = tr_input.start;
            tr_output.data  = tr_input.data.data;
            tx_channel      = tr_input.meta.data[$clog2(CHANNELS)-1 +16: 0 +16]; // if CHANNELS > 1

            if (tx_channel >= CHANNELS) begin
                string msg;
                $swrite(msg, "\n\tTX: Wrong channel num %0d Channel range is 0-%0d", tx_channel, CHANNELS-1);
                `uvm_fatal(this.get_full_name(), msg);
            end else begin
                `uvm_info(this.get_full_name(), $sformatf("\nTX send packet on channel %0d %s", tx_channel, tr_output.convert2string()), UVM_HIGH);
                tx_output[tx_channel].write(tr_output);
            end
        end
    endtask


    task rx_run(int unsigned index);
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)  tr_data;
        uvm_logic_vector::sequence_item #(1)                tr_discard;

        model_data#(ITEM_WIDTH, HDR_WIDTH) tr_out;
        string str_index;

        str_index.itoa(index);

        forever begin
            logic [16-1:0] pkt_size;
            const logic [8 -1:0] channel = index;


            rx_input[index].get(tr_data);
            rx_discard[index].get(tr_discard);
            if (tr_discard.data[0] == 1'b0) begin
                 tr_out = model_data#(ITEM_WIDTH, HDR_WIDTH)::type_id::create("tr_out", this);

                 //Add meta
                 tr_out = model_data#(ITEM_WIDTH, HDR_WIDTH)::type_id::create("tr_out", this);
                 tr_out.tag  =  {tr_data.tag, "CORE_TO_USER[", str_index, "]"};
                 tr_out.time_array_add(tr_data.start);
                 tr_out.time_array_add(tr_discard.start);
                 tr_out.data = tr_data;
                 pkt_size = tr_data.data.size();
                 tr_out.meta = uvm_logic_vector::sequence_item#(HDR_WIDTH)::type_id::create("tr_out_meta", this);
                 tr_out.meta.data = {channel, pkt_size};

                 rx_output.write(tr_out);
                `uvm_info(this.get_full_name(), $sformatf("\nRX Send packet on channel %0d %s", index, tr_data.convert2string()), UVM_HIGH);
            end else begin
                `uvm_info(this.get_full_name(), $sformatf("\nRX Discrad packet on channel %0d %s", index, tr_data.convert2string()), UVM_HIGH);
            end
        end
    endtask

    task run_phase(uvm_phase phase);
        for (int unsigned ch = 0; ch < CHANNELS; ch++) begin
            fork 
                automatic int unsigned index = ch;
                rx_run(index);
            join_none;
        end
        tx_run();
    endtask

endclass
