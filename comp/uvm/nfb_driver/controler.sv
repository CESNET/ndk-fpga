/*
 * file       : controler.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description:  common driver for nfb_tool
 * date       : 2022
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

// This class communicates with nfb_driver with POSIX messages.
// Function open create interface for communication with
// task serve communicate with nfb application until application is going to release connection.
//    If you want more application you can use forever begin controler.serve() end
// function close release system devices

class controler extends uvm_sequence;
    `uvm_object_utils(nfb_driver::controler)

    protected chandle       mq_id;
    protected int  unsigned port;
    protected string        dev_name;
    protected byte unsigned dtb[];
    protected bit           stop;

    function new (string name = "controler");
        super.new(name);
        mq_id = null;
        port  = 0;
    endfunction

    function void open(string dev_name);
        const string ip_addr = "0.0.0.0:";
        string dev_tree_name;
        stop    = 0;
        mq_id   = nfb_sv_create(ip_addr, port);
        $fflush();
        if (mq_id == null) begin
            `uvm_fatal("nfb_driver", {"\n\tCannot create grpc server ",  ip_addr, "\n\t\texample of address: \"0.0.0.0:\""})
        end

        dev_tree_name = $sformatf("%s_%0d", dev_name, port);
        if (this.tree_compile(dev_tree_name) == 0) begin
            `uvm_fatal("nfb_driver", {"\n\tCannot create device tree : ", dev_tree_name})
        end
        nfb_sv_set_fdt(mq_id, dtb);
    endfunction

    function void close();
        stop = 1;
    endfunction

    task serve(time wait_time = 100ns);
        int unsigned cmd;
        chandle      cmd_ptr;

        if (mq_id == null) begin
            `uvm_fatal("nfb_driver", "\n\tBefore you call server function you have to create grpc server");
        end

        do begin
            int unsigned size;
            logic [64-1:0] addr;
            byte unsigned data[];

            while((cmd_ptr = nfb_sv_cmd_get(mq_id, cmd, size, addr)) == null && stop == 0) begin
                #(wait_time);
            end
            cmd = stop ? 0 : cmd;
            case (cmd)
                0 : ; //program logout
                1 : nfb_sv_process(cmd_ptr, dtb);
                2 : begin
                    data = new[size];
                    nfb_sv_process(cmd_ptr, data);
                    this.write(addr, data);
                end
                3 : begin
                    data = new[size];
                    this.read(addr, data);
                    nfb_sv_process(cmd_ptr, data);
                end
                default : begin
                    `uvm_error(/*this.get_full_name()*/ "NULL", $sformatf("\n\tUnknown mi command type %0d", cmd));
                end
            endcase
        end while (!stop);

        nfb_sv_close(mq_id);
        mq_id = null;
    endtask

    function bit tree_compile(string name, string author = "anonymous", string revision = "0", string card_name = "NFB-VERIFICATION");
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
        $fwrite(dts, tree_components());
        $fwrite(dts, "\n    };\n  };\n};\n");
        $fclose(dts);

        if($system({"dtc -I dts -O dtb -o ", name, ".dtb ", name, ".dts"}) != 0) return 0;

        dtb_ptr = $fopen({name, ".dtb"}, "r");
        if (dtb_ptr == 0) return 0;
        $fread(dtb, dtb_ptr);
        $fclose(dtb_ptr);
        return 1;
    endfunction

    virtual function string tree_components();
        return "";
    endfunction

    virtual task write(logic [64-1:0] addr, byte unsigned data[]);
    endtask

    virtual task read(logic [64-1:0] addr, inout byte unsigned data[]);
    endtask
endclass

