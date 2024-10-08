/*
 * file       :  sequence_cfg.sv
 * Copyright (C) 2023 CESNET z. s. p. o.
 * description:  sequence configuration
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class sequence_cfg extends uvm_object;
    `uvm_object_utils(uvm_common::sequence_cfg)

    int unsigned transactions_count;

    function new(string name = "sequence_cfg");
        super.new(name);
        transactions_count = 0;
    endfunction

    function void pre_randomize();
        super.pre_randomize();
        transactions_count = 0;
    endfunction

    //return
    virtual function int unsigned next();
        return 1;
    endfunction

    //return 0 if sequence should stopp
    virtual function int unsigned stopped();
        return 0;
    endfunction

    virtual function string convert2string();
        return $sformatf("\n\tGenerated transactions %0d", transactions_count);
    endfunction
endclass

class sequence_cfg_transactions extends sequence_cfg;
    `uvm_object_utils(uvm_common::sequence_cfg_transactions)

    int unsigned transactions_min = 2000;
    int unsigned transactions_max = 4000;
    rand int unsigned transactions;

    constraint const_transatction {transactions inside {[transactions_min:transactions_max]};
                                  }

    function new(string name = "sequence_cfg_base");
        super.new(name);
    endfunction

    //return
    virtual function int unsigned next();
        const int unsigned ret = (transactions_count < transactions);
        transactions_count++;
        return ret;
    endfunction

    //return 0 if sequence should stopp
    virtual function int unsigned stopped();
        return !(transactions_count < transactions);
    endfunction
endclass


class sequence_cfg_signal extends sequence_cfg;
    `uvm_object_utils(uvm_common::sequence_cfg_signal)

    int unsigned stop;

    function new(string name = "sequence_cfg_base");
        super.new(name);
        stop = 0;
    endfunction

    function void clear();
        stop = 0;
    endfunction


    function void send_stop();
        stop = 1;
    endfunction

    //return
    virtual function int unsigned next();
        transactions_count++;
        return !stop;
    endfunction

    //return 0 if sequence should stopp
    virtual function int unsigned stopped();
        return stop;
    endfunction
endclass


////////////////////////////////////////////////////////////////
// FOR IF you need same number of transaction to stopp
////////////////////////////////////////////////////////////////
class sequence_cfg_data extends uvm_object;
    `uvm_object_utils(uvm_common::sequence_cfg_data)

    int unsigned stop;
    int unsigned transactions[];
    static int unsigned obj_num = 0;
    int unsigned tisk;

    function new(string name = "sequence_cfg_base");
        super.new(name);
        this.clear();


        tisk = obj_num;
        obj_num++;
    endfunction

    function void send_stop();
        stop = 1;
    endfunction

    function void clear();
        stop = 0;
        for (int unsigned it = 0; it < transactions.size(); it++) begin
            transactions[it] = 0;
        end
    endfunction

    function int unsigned next(int unsigned seq_num);
        transactions[seq_num]++;
        return !this.stopped(seq_num);
    endfunction

    function int unsigned stopped(int unsigned seq_num);
        int unsigned ret    = this.stop;
        int unsigned tr_max = transactions[0];
        for (int unsigned it = 1; it < transactions.size(); it++) begin
           tr_max = (tr_max >= transactions[it]) ? tr_max : transactions[it];
        end
        return this.stop && (tr_max == transactions[seq_num]);
    endfunction
endclass

class sequence_cfg_index extends sequence_cfg;
    `uvm_object_utils(uvm_common::sequence_cfg_index)

    int unsigned index;
    sequence_cfg_data data;

    function new(string name = "sequence_cfg_base");
        super.new(name);
        data = null;
    endfunction

    function void data_set(sequence_cfg_data data, int unsigned index);
        this.data  = data;
        this.index = index;
    endfunction

    //return
    virtual function int unsigned next();
        return data.next(index);
    endfunction

    //return 0 if sequence should stopp
    virtual function int unsigned stopped();
        return data.stopped(index);
    endfunction
endclass

class sequences_cfg_sync#(int unsigned NUM) extends sequence_cfg;
    `uvm_object_param_utils(uvm_common::sequences_cfg_sync#(NUM))

    sequence_cfg_data  data;
    sequence_cfg_index cfg[NUM];

    function new(string name = "sequence_cfg_base");
        super.new(name);
        data = sequence_cfg_data::type_id::create({name, ".data"});
        data.transactions = new[NUM];
        for (int unsigned it = 0; it < NUM; it++) begin
            data.transactions[it] = 0;
            cfg[it] = sequence_cfg_index::type_id::create({name, $sformatf(".cfg_%0d", it)});
            cfg[it].data_set(data, it);
        end
    endfunction

    function void send_stop();
        data.send_stop();
    endfunction

    //return
    virtual function int unsigned next();
        return !data.stop;
    endfunction

    //return 0 if sequence should stopp
    virtual function int unsigned stopped();
        int unsigned ret = data.stop;
        int unsigned tr  = data.transactions[0];
        for (int unsigned it = 1; it < data.transactions.size(); it++) begin
           ret &= (tr == data.transactions[it]);
        end
        return ret;
    endfunction
endclass

