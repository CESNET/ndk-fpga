// meter.sv: measure pcie statistic
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


// Definition of mfb monitor
class stats  extends uvm_subscriber#(uvm_pcie::header);
    `ndk_component_utils(uvm_pcie::stats)

    localparam KOEF = 32;

    // ------------------------------------------------------------------------
    // Parameters
    //int unsigned error_speed; //In items
    protected int unsigned       packets;
    protected uvm_common::stats  speed;
    protected uvm_common::stats  data_size;
    protected time               last_update;

    protected time               section_time;

    // ------------------------------------------------------------------------
    // Constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
        speed       = new();
        data_size   = new();

        section_time = 500us;
    endfunction

    // ------------------------------------------------------------------------
    // Functions
    virtual function void write(uvm_pcie::header t);
        int unsigned tmp_data_size;
        const time update_time_new = $time;
        int unsigned divider;
        packets += 1;

        tmp_data_size = t.data.size();

        data_size.next_val(tmp_data_size);
        divider = (update_time_new - last_update)/1ns;
        divider = (divider != 0) ? divider : 1;
        speed.next_val(real'(tmp_data_size)/divider);
        last_update = update_time_new;
    endfunction

    task run_phase(uvm_phase phase);
        time information_stop;
        last_update = $time;

        //in inicialization this become start
        information_stop = $time;
        forever begin
            time information_start;
            real min;
            real max;
            real avg;
            real std_dev;
            string msg;

            //Init section
            information_start = information_stop;
            packets = 0;
            speed.reset();
            data_size.reset();

            #(section_time);
            information_stop = $time;

            // verilog_lint: waive line-length
            msg = $sformatf("\nPCIE meter information time [%0dns, %0dns]\n", information_start/1ns, information_stop/1ns);
            msg = {msg, $sformatf("\n\tpacket %0d", packets)};
            data_size.count(min, max, avg, std_dev);
            msg = {
                msg,
                $sformatf(
                    "\n\tDATA:\n\t\tMIN : %0.2f (%0.2f b) \n\t\tMAX : %0.2f (%0.2f b)\n\t\tAVG STD_DEV : %0.2f %0.2f (%0.2f b %0.2f b)\n"
                        ,
                    min,
                    min * KOEF,
                    max,
                    max * KOEF,
                    avg,
                    std_dev,
                    avg * KOEF,
                    std_dev * KOEF
                )
            };
            speed.count(min, max, avg, std_dev);
            msg = {
                msg,
                $sformatf(
                    "\tSPEED :\n\t\tMIN : %0.2f Gb/s \n\t\tMAX : %0.2f Gb/s\n\t\tAVG STD_DEV : %0.2f Gb/s %0.2f Gb/s\n",
                    min * KOEF,
                    max * KOEF,
                    avg * KOEF,
                    std_dev * KOEF
                )
            };
            `uvm_info(this.get_full_name(), msg, UVM_LOW);
        end
    endtask

endclass
