/*
 * file       : data.sv
 * Copyright (C) 2023 CESNET z. s. p. o.
 * description: callback remove data from one fifo and put into other
 * date       : 2023
 * authors    : Radek Iša <isa@cesnet.ch>
 *            : Oliver Gurka <oliver.gurka@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class cbs_simple #(int unsigned DATA_WIDTH) extends uvm_event_callback;
    `uvm_object_param_utils(uvm_probe::cbs_simple #(DATA_WIDTH))

    protected logic [DATA_WIDTH-1:0] out[$];

    function new(string name = "");
        super.new(name);
    endfunction

    //---------------------------------------
    // pre trigger method
    //---------------------------------------
    virtual function bit pre_trigger(uvm_event e, uvm_object data);
        return 0;
    endfunction

    //---------------------------------------
    // post trigger method
    //---------------------------------------
    virtual function void post_trigger(uvm_event e, uvm_object data);
        uvm_probe::data#(DATA_WIDTH) c_data;

        $cast(c_data, data);
        out.push_back(c_data.data);
    endfunction

    //---------------------------------------
    // OTHERS METHODS
    //---------------------------------------
    task get(output logic [DATA_WIDTH-1:0] dut_info);
        wait(out.size() != 0);
        dut_info = out.pop_front();
    endtask

    function int unsigned used();
        return (out.size() != 0);
    endfunction
endclass

class cbs_fifo#(type T_TYPE, int unsigned DATA_WIDTH) extends uvm_event_callback;
    `uvm_object_param_utils(uvm_probe::cbs_fifo#(T_TYPE, DATA_WIDTH))

    protected typedef struct {
        T_TYPE                 model;
        logic [DATA_WIDTH-1:0] dut;
    } t_output;

    uvm_common::fifo#(T_TYPE)    in;
    protected mailbox#(t_output) out;

    function new(string name = "");
        super.new(name);
        out = new();
    endfunction

    //---------------------------------------
    // pre trigger method
    //---------------------------------------
    virtual function bit pre_trigger(uvm_event e,uvm_object data);
        return 0;
    endfunction

    //---------------------------------------
    // post trigger method
    //---------------------------------------
    virtual function void post_trigger(uvm_event e,uvm_object data);
        uvm_probe::data#(DATA_WIDTH) c_data;
        T_TYPE   input_item;
        t_output output_item;

        $cast(c_data, data);
        in.try_get(input_item);
        if (input_item == null) begin
            `uvm_warning(this.get_full_name(), $sformatf("\n\tEvent on unknown item %h\n", c_data.data));
        end else begin
            output_item.model = input_item;
            output_item.dut   = c_data.data;
            if (out.try_put(output_item) == 0) begin
                `uvm_fatal(this.get_full_name(), $sformatf("\n\tCannot put event %h into queue\n", c_data.data));
            end
        end
    endfunction

    //---------------------------------------
    // OTHERS METHODS
    //---------------------------------------
    task get(output T_TYPE tr, logic [DATA_WIDTH-1:0] dut_info);
        t_output tr_tmp;
        out.get(tr_tmp);
        tr       = tr_tmp.model;
        dut_info = tr_tmp.dut;
    endtask

    function int unsigned used();
        return (out.num() != 0);
    endfunction
endclass


class cbs_msgbox#(type T_TYPE, int unsigned DATA_WIDTH) extends uvm_event_callback;
    `uvm_object_param_utils(uvm_probe::cbs_msgbox#(T_TYPE, DATA_WIDTH))

    protected typedef struct {
        T_TYPE                 model;
        logic [DATA_WIDTH-1:0] dut;
    } t_output;

    protected mailbox#(T_TYPE)   in;
    protected mailbox#(t_output) out;

    function new(string name = "");
        super.new(name);
        in  = new();
        out = new();
    endfunction

    //---------------------------------------
    // pre trigger method
    //---------------------------------------
    virtual function bit pre_trigger(uvm_event e,uvm_object data);
        return 0;
    endfunction

    //---------------------------------------
    // post trigger method
    //---------------------------------------
    virtual function void post_trigger(uvm_event e,uvm_object data);
        uvm_probe::data#(DATA_WIDTH) c_data;
        T_TYPE   input_item;
        t_output output_item;

        $cast(c_data, data);
        if (in.try_get(input_item) == 1'b0) begin
            `uvm_warning(this.get_full_name(), $sformatf("\n\tEvent on unknown item %h\n", c_data.data));
        end else begin
            output_item.model = input_item;
            output_item.dut   = c_data.data;
            if (out.try_put(output_item) == 0) begin
                `uvm_fatal(this.get_full_name(), $sformatf("\n\tCannot put event %h into queue\n", c_data.data));
            end
        end
    endfunction


    function void try_put(T_TYPE tr);
        void '(in.try_put(tr));
    endfunction

    //---------------------------------------
    // OTHERS METHODS
    //---------------------------------------
    task get(output T_TYPE tr, logic [DATA_WIDTH-1:0] dut_info);
        t_output tr_tmp;
        out.get(tr_tmp);
        tr       = tr_tmp.model;
        dut_info = tr_tmp.dut;
    endtask

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (in.num != 0);
        ret |= (out.num() != 0);
        return ret;
    endfunction
endclass
