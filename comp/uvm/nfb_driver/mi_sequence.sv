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

    function new (string name = "controler");
        int pid;
        super.new(name);
    endfunction

    //parameter dev tree is deprecated and can be deleted anytime
    function void component_set(uvm_mem comp, string dev_tree = "");
        this.mem      = comp;

        // preocess deprecated parameter dev_tree
        if (devtree == null) begin
            const string dt_name = $sformatf("dev_tree_deprecated_%0d", $urandom_range(0, 50000));
            int dtb_ptr;
            if(this.tree_compile(dt_name, dev_tree) == 0) begin
                `uvm_fatal(this.get_full_name(), "\n\ŧCannot create and compile device tree");
            end
            devtree = new({dt_name, ".dtb"});
        end
    endfunction

    // this function is deprecated and can be deleted anytime
    function bit tree_compile(string name, string dev_tree);
        const string author = "anonymous";
        const string revision = "-1";
        const string card_name = "NFB-VERIFICATION";
        int dts;
        int dtb_ptr;

        dts = $fopen({name, ".dts"}, "w");
        if(dts == 0) return 0;
        $fwrite(dts, "/dts-v1/;\n\n");
        $fwrite(dts, "/ {\n\n");
        $fwrite(dts, "  firmware {\n");
        $fwrite(dts, "    build-tool = \"ModelSim\";\n");
        $fwrite(dts, "    build-author = \"%s\";\n", author);
        $fwrite(dts, "    build-revision = \"%s\";\n", revision);
        $fwrite(dts, "    build-time = <0x0>;\n");
        $fwrite(dts, "    card-name = \"%s\";\n\n", card_name);
        $fwrite(dts, "    mi0: mi_bus {\n");
        $fwrite(dts, "      compatible = \"netcope,bus,mi\";\n");
        $fwrite(dts, "      resource = \"PCI0,BAR0\";\n");
        $fwrite(dts, "      width = <0x20>;\n");
        $fwrite(dts, "      #address-cells = <1>;\n");
        $fwrite(dts, "      #size-cells = <1>;\n\n");
        $fwrite(dts, dev_tree);
        $fwrite(dts, "\n    };\n  };\n};\n");
        $fclose(dts);

        if($system({"dtc -I dts -O dtb -o ", name, ".dtb ", name, ".dts"}) != 0) return 0;
        return 1;
    endfunction

    virtual task run_program();
    endtask

    task body();
        //Create interface
        this.open();
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



