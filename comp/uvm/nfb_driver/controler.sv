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
    nfb_driver::dev_tree    devtree;
    protected bit           stop;

    function new (string name = "controler");
        super.new(name);
        mq_id = null;
        port  = 0;

        if (uvm_config_db#(nfb_driver::dev_tree)::get(null, "", "DevTree", devtree) == 0) begin
            devtree = null;
            //`uvm_fatal(this.get_full_name() , $sformatf("\n\t%s\n\tCannot get device tree", `__FILE__));
        end
    endfunction

    function void open();
        const string ip_addr = "0.0.0.0:0";
        stop    = 0;
        mq_id   = nfb_sv_create(ip_addr, port);
        $fflush();
        if (mq_id == null) begin
            `uvm_fatal(
                m_sequencer != null ? m_sequencer.get_full_name() : "null" ,
                {"\n\tCannot create grpc server ",  ip_addr, "\n\t\texample of address: \"0.0.0.0:0\""}
            )
        end

        nfb_sv_set_fdt(mq_id, devtree.data);
    endfunction

    function void close();
        stop = 1;
    endfunction

    task serve(time wait_time = 100ns);
        int unsigned cmd;
        chandle      cmd_ptr;

        if (mq_id == null) begin
            const string msg = "\n\tBefore you call server function you have to create grpc server";
            `uvm_fatal(m_sequencer.get_full_name(), msg);
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
                1 : nfb_sv_process(cmd_ptr, devtree.data);
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
        // verilog_lint: waive explicit-begin
        end while (!stop);

        nfb_sv_close(mq_id);
        mq_id = null;
    endtask

    virtual task write(logic [64-1:0] addr, byte unsigned data[]);
    endtask

    virtual task read(logic [64-1:0] addr, inout byte unsigned data[]);
    endtask
endclass

