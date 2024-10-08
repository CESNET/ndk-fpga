/*
 * file       : mi_sequence.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: common driver for nfb_tool
 * date       : 2022
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

// This class Program convert write and read requenset to request for uvm_memory

class mi_sequence extends controler;
    `uvm_object_utils(nfb_driver::mi_sequence)

    protected uvm_mem mem;
    protected string  dev_tree;
    protected string  inf_name;

    function new (string name = "controler");
        int pid;
        super.new(name);

        inf_name = "nic";
    endfunction

    function void component_set(uvm_mem comp, string dev_tree);
        this.mem      = comp;
        this.dev_tree = dev_tree;
    endfunction

    virtual function string tree_components();
        return dev_tree;
    endfunction

    virtual task run_program();
    endtask

    //virtual task run_backhand();
    //    this.serve();
    //endtask

    task body();
        //Create interface
        this.open(inf_name);
        fork
            this.serve();
        join_none

        this.run_program();
        this.close();
    endtask


    virtual task write(logic [64-1:0] addr, byte unsigned data[]);
        int unsigned   burst_size;
        int unsigned   index_it;
        int unsigned   index_jt;
        uvm_status_e   status;
        uvm_reg_addr_t offset;
        uvm_reg_data_t value[];

        offset     = (addr - mem.get_address())/mem.get_n_bytes();
        burst_size = (data.size() + mem.get_n_bytes() -1)/mem.get_n_bytes();
        value = new[burst_size];

        index_it = 0;
        index_jt = 0;
        for (int unsigned it = 0; it < data.size(); it++) begin
            value[index_it][(index_jt+1)*8-1 -: 8] = data[it];
            index_jt ++;
            if (index_jt >= mem.get_n_bytes()) begin
                index_it++;
                index_jt = 0;
            end
        end
        mem.burst_write(status, offset, value);
    endtask

    virtual task read(logic [64-1:0] addr, inout byte unsigned data[]);
        int unsigned   burst_size;
        int unsigned   index_it;
        int unsigned   index_jt;
        uvm_status_e   status;
        uvm_reg_addr_t offset;
        uvm_reg_data_t value[];

        offset = (addr - mem.get_address())/mem.get_n_bytes();
        burst_size = (data.size() + mem.get_n_bytes() -1)/mem.get_n_bytes();
        value = new[burst_size];

        mem.burst_read(status, offset, value);

        index_it = 0;
        index_jt = 0;
        for (int unsigned it = 0; it < data.size(); it++) begin
            data[it] = value[index_it][(index_jt+1)*8-1 -: 8];
            index_jt ++;
            if (index_jt >= mem.get_n_bytes()) begin
                index_it++;
                index_jt = 0;
            end
        end
   endtask
endclass



