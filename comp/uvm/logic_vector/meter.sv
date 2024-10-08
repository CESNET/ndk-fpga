// meter.sv: Logic vector speed meter
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class meter #(int unsigned ITEM_WIDTH) extends uvm_subscriber#(sequence_item #(ITEM_WIDTH));
    `uvm_component_param_utils(uvm_logic_vector::meter #(ITEM_WIDTH))

    // ------------------------------------------------------------------------
    // Parameters

    protected uvm_common::stats  speed; //In items
    protected int unsigned       words;
    protected int unsigned       sections;
    protected time               section_time;
    protected time               start_time;

    // ------------------------------------------------------------------------
    // Constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
        sections = 20;
        section_time = 10us;
        words = 0;
    endfunction

    // ------------------------------------------------------------------------
    // Functions
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        speed = new();
    endfunction;

    virtual function void write(sequence_item #(ITEM_WIDTH) t);
        words += 1;
    endfunction


    task run_phase(uvm_phase phase);
        int unsigned sections_it;

        sections_it = 0;
        start_time  = $time();
        forever begin
            #(section_time);
            sections_it++;

            speed.next_val((real'(words)/(section_time/1000ms))/1000000.0);
            words = 0;

            if (sections_it == sections) begin
                string msg;
                time stop_time = $time();
                real min;
                real max;
                real avg;
                real std_dev;

                msg = $sformatf("\nMeter information time [%0dns, %0dns]\n", start_time/1ns, stop_time/1ns);

                speed.count(min, max, avg, std_dev);
                msg = {msg, $sformatf("\tspeed :\n\t\tMIN : %0.2f MT/s \n\t\tMAX : %0.2f MT/s\n\t\tAVG STD_DEV : %0.2f MT/s %0.2f MT/s\n", min, max, avg, std_dev)};

                `uvm_info(this.get_full_name(), msg, UVM_LOW);
                speed.reset();
                sections_it = 0;
                start_time  = stop_time;
            end
        end
    endtask

    function void report_phase(uvm_phase phase);
        string msg;
        real min;
        real max;
        real avg;
        real std_dev;
        time stop_time;
        time diff;

        super.report_phase(phase);

        stop_time = $time;
        diff = stop_time - start_time;

        speed.next_val((real'(words)/(diff/1000ms))/1000000.0);
        msg = $sformatf("\nMeter information time [%0dns, %0dns]\n", start_time/1ns, stop_time/1ns);
        speed.count(min, max, avg, std_dev);
        msg = {msg, $sformatf("\tspeed :\n\t\tMIN : %0.2f MT/s \n\t\tMAX : %0.2f MT/s\n\t\tAVG STD_DEV : %0.2f MT/s %0.2f MT/s\n", min, max, avg, std_dev)};
        `uvm_info(this.get_full_name(), msg, UVM_LOW);
    endfunction
endclass
