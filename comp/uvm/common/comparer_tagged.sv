/*
 * file       : comparer_base_taged.sv
 * Copyright (C) 2023 CESNET z. s. p. o.
 * description: this component compares two output transactions with same tag ID in order. IF component stays
 *              too long in fifo then errors are going to occur.
 * date       : 2023
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class comparer_fifo #(type MODEL_ITEM, type DUT_ITEM = MODEL_ITEM);

    protected MODEL_ITEM model_items[$];
    protected DUT_ITEM model_items_last;
    int unsigned       compared;
    int unsigned       errors;

    function new();
        compared = 0;
        errors   = 0;
        model_items_last = new();
    endfunction

    function void push_back(MODEL_ITEM item);
        model_items.push_back(item);
    endfunction

    function MODEL_ITEM get(int unsigned index);
        if (model_items.size() == 0) begin
            return null;
        end
        return model_items[index];
    endfunction

    function DUT_ITEM dut_last();
        return model_items_last;
    endfunction

    function void dut_last_set(DUT_ITEM tr);
        model_items_last = tr;
    endfunction

    function int unsigned size();
        return model_items.size();
    endfunction

    function void clear();
        model_items.delete();
    endfunction

    function void delete(int unsigned it);
        model_items.delete(it);
    endfunction
endclass


virtual class comparer_base_tagged #(type MODEL_ITEM, type DUT_ITEM = MODEL_ITEM) extends comparer_base#(MODEL_ITEM, DUT_ITEM);

    int unsigned             model_accept;
    comparer_fifo #(MODEL_ITEM, DUT_ITEM) model_items[string];
    int unsigned             dut_errors;
    int unsigned             dut_accept;
    DUT_ITEM dut_items[$];


    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        model_accept = 0;
        dut_accept   = 0;
        dut_errors   = 0;
    endfunction

    virtual function void flush();
        int unsigned index_valid;
        string index;

        index_valid = model_items.first(index);
        while (index_valid != 0) begin
            model_items[index].clear();
            index_valid = model_items.next(index);
        end
        dut_items.delete();
    endfunction

    virtual function int unsigned used();
        int unsigned ret = 0;
        int unsigned index_valid;
        string index;

        index_valid = model_items.first(index);
        while (index_valid != 0) begin
            ret |= (model_items[index].size() != 0);
            index_valid = model_items.next(index);
        end
        ret |= (dut_items.size() != 0);

        return ret;
    endfunction

    virtual function int unsigned success();
        int unsigned ret = 1;
        int unsigned index_valid;
        string index;

        ret &= (dut_errors == 0);
        index_valid = model_items.first(index);
        while (index_valid != 0) begin
            ret &= (model_items[index].errors == 0);
            index_valid = model_items.next(index);
        end
        return ret;
   endfunction

    virtual function void write_model(MODEL_ITEM tr);
        int unsigned w_end = 0;
        int unsigned it    = 0;

        model_accept++;
        `uvm_info(this.get_full_name(), $sformatf("\n\tGet model transactions %0d in time %0dns\n%s\n",
                  model_accept, $time()/1ns, model_item2string(tr)), UVM_FULL);

        if (model_items.exists(tr.tag) == 0) begin
            model_items[tr.tag] = new();
        end

        while (it < dut_items.size() && w_end == 0) begin
            w_end = compare(tr, dut_items[it]);
            if (w_end == 0) begin
                it++;
            end else begin
                DUT_ITEM dut_last;
                `uvm_info(this.get_full_name(), $sformatf("\n\tTransaction Match DUT(%0d) Model(%0d) output time %0dns\nMODEL ITEM : %s\nDUT ITEM : %s",
                    dut_items[it].get_transaction_id(), model_accept, dut_items[it].time_last()/1ns,
                    model_item2string(tr), dut_item2string(dut_items[it])), UVM_DEBUG);

                dut_last = model_items[tr.tag].dut_last();
                if (dut_last.time_last() > dut_items[it].time_last()) begin

                    string msg;
                    msg = $sformatf("\n\tSome transaction %0d what have output time %0dns have been outruned by transaction %0d  with otput time %0dns\n\ttag %s\nOutrun transaction\n%s\nOutruned transaction\n%s\n",
                            dut_last.get_transaction_id(), dut_last.time_last()/1ns, dut_items[it].get_transaction_id(),
                            dut_items[it].time_last()/1ns, tr.tag,
                            dut_item2string(dut_last),
                            dut_item2string(dut_items[it]));
                    `uvm_error(this.get_full_name(), msg);
                end

                model_items[tr.tag].dut_last_set(dut_items[it]);
                model_items[tr.tag].compared++;
                dut_items.delete(it);
            end
        end

        if (w_end == 0) begin
            model_items[tr.tag].push_back(tr);
        end
    endfunction

    virtual function void write_dut(DUT_ITEM tr);
        int unsigned w_end = 0;
        int unsigned it    = 0;
        int unsigned index_valid;
        string index;
        MODEL_ITEM model_tr;

        dut_accept += 1;
        `uvm_info(this.get_full_name(), $sformatf("\n\tGet DUT transactions %0d in time %0dns\n%s\n", dut_accept, $time()/1ns, dut_item2string(tr)), UVM_FULL);

        //try get item from DUT
        index_valid = model_items.first(index);
        if (index_valid != 0) begin
            model_tr    = model_items[index].get(0);
        end

        while (index_valid != 0 && (model_tr == null || compare(model_tr, tr) == 0)) begin
            index_valid = model_items.next(index);
            model_tr    = model_items[index].get(0);
        end

        if (index_valid != 0) begin
            comparer_fifo #(MODEL_ITEM, DUT_ITEM) cmp_fifo = model_items[index];
            MODEL_ITEM               model_item = cmp_fifo.get(0);

            cmp_fifo.compared++;

            `uvm_info(this.get_full_name(), $sformatf("\n\tTransaction Match DUT %0d output time %0dns\nMODEL ITEM : %s\nDUT ITEM : %s\n",
                dut_accept, $time()/1ns, model_item2string(model_item), dut_item2string(tr)), UVM_DEBUG);

            cmp_fifo.dut_last_set(tr);
            cmp_fifo.delete(0);
        end else begin
            dut_items.push_back(tr);
        end
    endfunction

    function string dut_tr_get(MODEL_ITEM tr, time tr_time);
        string msg = "";
        for (int unsigned it = 0; it < dut_items.size(); it++) begin
            msg = {msg, $sformatf("\n\nOutput time %0dns (%0dns) \nMODEL ITEM : %s\nDUT ITEM %s\n", dut_items[it].time_last()/1ns, (dut_items[it].time_last() - tr_time)/1ns, model_item2string(tr), dut_item2string(dut_items[it]))};
        end
        return msg;
    endfunction

    function string model_tr_get(DUT_ITEM tr);
        int unsigned index_valid;
        string index;
        string msg = "";

        index_valid = model_items.first(index);
        while (index_valid != 0) begin
            for (int unsigned it = 0; it < model_items[index].size(); it++) begin
                MODEL_ITEM tmp_item = model_items[index].get(it);
                msg = {msg, $sformatf("\n\nTag %s\nMODEL ITEM : %s\nDUT ITEM : %s\n", index, model_item2string(tmp_item), dut_item2string(tr))};
            end
            //next index
            index_valid = model_items.next(index);
        end

        return msg;
    endfunction

    task run_model_delay_check();
        time delay;
        int unsigned index_valid;
        string index;

        forever begin
            time   delay_max;

            index_valid = model_items.first(index);
            delay_max   = 0ns;
            while (index_valid != 0) begin
                if (model_items[index].size() != 0) begin
                    delay = $time() - model_items[index].get(0).time_last();
                end else begin
                    delay = 0ns;
                end

                if (delay > delay_max) begin
                    delay_max = delay;
                end

                if (delay >= dut_tr_timeout) begin
                    comparer_fifo #(MODEL_ITEM, DUT_ITEM) cmp_fifo = model_items[index];
                    MODEL_ITEM               model_tr = cmp_fifo.get(0);

                    cmp_fifo.errors++;
                    `uvm_error(this.get_full_name(), $sformatf("\n\tTransaction from DUT is delayed %0dns. Probably stuck.\n\tErrors/Compared %0d/%0d\n%s\n\nDUT transactions:\n%s",
                                                         cmp_fifo.errors, cmp_fifo.compared, delay/1ns, model_item2string(model_tr),
                                                         this.dut_tr_get(model_tr, model_tr.time_last())));
                    cmp_fifo.delete(0);
                end

                index_valid = model_items.next(index);
            end

            if (dut_tr_timeout > delay) begin
                #(dut_tr_timeout - delay);
            end else begin
                #(200ns);
            end
        end
    endtask

    task run_dut_delay_check();
        time delay;
        forever begin
            wait(dut_items.size() > 0);
            delay = $time() - dut_items[0].time_last();
            if (delay >= model_tr_timeout) begin
                 dut_errors++;
                `uvm_error(this.get_full_name(), $sformatf("\n\tTransaction %0d from DUT is unexpected.\n\tErrors %0d Output time %0dns. Delay %0dns. Probably unexpected transaction.\n%s\n\n%s",
                                                           dut_items[0].get_transaction_id(), dut_errors, dut_items[0].time_last()/1ns, delay/1ns,
                                                           dut_item2string(dut_items[0]), this.model_tr_get(dut_items[0])));
                dut_items.delete(0);
            end else begin
                #(model_tr_timeout - delay);
            end
        end
    endtask

    virtual function string info(logic data = 0);
        int unsigned index_valid;
        string index;
        string msg = "";
        index_valid = model_items.first(index);
        msg = {msg, $sformatf("\n\tErrors %0d", dut_errors)};
        while (index_valid != 0) begin
            msg = {msg, $sformatf("\n\tTag %s Errors/Compared %0d/%0d transactions", index, model_items[index].errors, model_items[index].compared)};
            if (data == 1) begin
                for (int unsigned it = 0; it < model_items[index].size(); it++) begin
                    msg = {msg, $sformatf("\n\tModels transaction : %0d", it), model_item2string(model_items[index].get(it))};
                end
            end
            //next index
            index_valid = model_items.next(index);
        end

        if (data == 1) begin
            for (int unsigned it = 0; it < dut_items.size(); it++) begin
                msg = {msg, $sformatf("\n\tDUT transaction : %0d", it), dut_item2string(dut_items[it])};
            end
        end
        return msg;
    endfunction
endclass
