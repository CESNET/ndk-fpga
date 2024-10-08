//-- model.sv: Model of implementation
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša  <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class model #(ITEM_WIDTH, META_WIDTH, CHANNELS) extends uvm_component;
    `uvm_component_param_utils(uvm_splitter_simple::model#(ITEM_WIDTH, META_WIDTH, CHANNELS))

    localparam SEL_WIDTH = $clog2(CHANNELS);

    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))               in_data;
    uvm_tlm_analysis_fifo#(uvm_logic_vector::sequence_item #($clog2(CHANNELS) + META_WIDTH)) in_meta;

    uvm_analysis_port #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) out_data[CHANNELS];
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(META_WIDTH))      out_meta[CHANNELS];

    protected uvm_logic_vector::sequence_item #($clog2(CHANNELS) + META_WIDTH) headers[$];

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        in_data = new("in_data", this);
        in_meta = new("in_meta", this);
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            string str_it;

            str_it.itoa(it);
            out_data[it] = new({"out_data_", str_it}, this);
            out_meta[it] = new({"out_meta_", str_it}, this);
        end
    endfunction

    function void reset();
       in_data.flush();
       in_meta.flush();
       headers.delete();
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (in_data.used() != 0);
        ret |= (in_meta.used() != 0);
        ret |= (headers.size() != 0);
        return ret;
    endfunction

    task run_meta(uvm_phase phase);
        forever begin
            uvm_logic_vector::sequence_item #($clog2(CHANNELS) + META_WIDTH) tr_in;
            uvm_logic_vector::sequence_item #(META_WIDTH)                    tr_out;
            int unsigned channel;
            string msg;

            in_meta.get(tr_in);
            if (this.get_report_verbosity_level() >= UVM_FULL) begin
                msg = tr_in.convert2string();
            end else begin
                msg = "";
            end

            //save it for data
            headers.push_back(tr_in);
            //Create output header
            tr_out = uvm_logic_vector::sequence_item #(META_WIDTH)::type_id::create("tr_output_meta", this);
            tr_out.start = tr_in.start;
            tr_out.data  = tr_in.data[META_WIDTH-1:0];
            channel      = tr_in.data[SEL_WIDTH + META_WIDTH-1 : META_WIDTH];

            if (channel >= CHANNELS) begin
                string msg;
                msg = $sformatf( "\n\tWrong channel num %0d Channel range is 0-%0d", channel, CHANNELS-1);
                `uvm_fatal(this.get_full_name(), msg);
            end else begin
                `uvm_info(this.get_full_name(), $sformatf("\nINPUT\n\t%s\nOUTPUT : \n%s\n\n", msg, tr_out.convert2string()), UVM_HIGH);
                out_meta[channel].write(tr_out);
            end
        end
    endtask

    task run_data(uvm_phase phase);
        forever begin
            uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) tr_in;
            uvm_logic_vector::sequence_item #($clog2(CHANNELS) + META_WIDTH) tr_in_meta;
            uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) tr_out;
            int unsigned channel;
            string msg;

            in_data.get(tr_in);
            wait (headers.size != 0);
            tr_in_meta = headers.pop_front();
            if (this.get_report_verbosity_level() >= UVM_FULL) begin
                msg = $sformatf("\nMeta %s\nDATA\n%s\n", tr_in.convert2string(), tr_in_meta.convert2string());
            end else begin
                msg = "";
            end

            tr_out = uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)::type_id::create("tr_out" ,this);
            tr_out.start = tr_in.start;
            tr_out.time_array_add(tr_in_meta.start);
            tr_out.data = tr_in.data;
            channel     = tr_in_meta.data[SEL_WIDTH + META_WIDTH-1 : META_WIDTH];

            if (channel >= CHANNELS) begin
                string msg;
                msg = $sformatf( "\n\tWrong channel num %0d Channel range is 0-%0d", channel, CHANNELS-1);
                `uvm_fatal(this.get_full_name(), msg);
            end else begin
                `uvm_info(this.get_full_name(), $sformatf("\nINPUT\n\t%s\nOUTPUT : \n%s\n\n", msg, tr_out.convert2string()), UVM_HIGH);
                out_data[channel].write(tr_out);
            end
        end
    endtask

    task run_phase(uvm_phase phase);
        fork
            run_data(phase);
            run_meta(phase);
        join
    endtask
endclass
