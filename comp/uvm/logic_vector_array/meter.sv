//-- monitor.sv: Mfb monitor
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of mfb monitor
class meter #(int unsigned ITEM_WIDTH) extends uvm_subscriber#(sequence_item #(ITEM_WIDTH));
    `uvm_component_param_utils(uvm_logic_vector_array::meter #(ITEM_WIDTH))

    localparam KOEF = ITEM_WIDTH;

    // ------------------------------------------------------------------------
    // Parameters
    //int unsigned error_speed; //In items
    protected uvm_common::stats  speed; //In items
    protected uvm_common::stats  data_size; // In items
    protected int unsigned       block_data_size;
    protected int unsigned       sections;
    protected time               section_time;

    // ------------------------------------------------------------------------
    // Constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
        sections = 50;
        section_time = 10us;
    endfunction

    // ------------------------------------------------------------------------
    // Functions
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        speed = new();
        data_size = new();
        block_data_size = 0;
    endfunction;

    virtual function void write(sequence_item #(ITEM_WIDTH) t);
        data_size.next_val(t.size());
        block_data_size += t.size();
    endfunction


    task run_phase(uvm_phase phase);
        int unsigned sections_it;
        time start_time;

        sections_it = 0;
        start_time  = $time();
        forever begin
            #(section_time);
            sections_it++;

            speed.next_val(real'(block_data_size)/(section_time/1ns));
            block_data_size = 0;

            if (sections_it == sections) begin
                string msg;
                time stop_time = $time();
                real min;
                real max;
                real avg;
                real std_dev;

                msg = $sformatf("\nMeter information time [%0dns, %0dns]\n", start_time/1ns, stop_time/1ns);
                data_size.count(min, max, avg, std_dev);
                msg = {msg, $sformatf("\tData size:\n\t\tMIN : %0.2f (%0.2f B) \n\t\tMAX : %0.2f (%0.2f B)\n\t\tAVG STD_DEV : %0.2f %0.2f (%0.2f B %0.2f B)\n", min, min*KOEF, max, max*KOEF, avg, std_dev, avg*KOEF, std_dev*KOEF)};

                speed.count(min, max, avg, std_dev);
                msg = {msg, $sformatf("\tspeed :\n\t\tMIN : %0.2f Gb/s \n\t\tMAX : %0.2f Gb/s\n\t\tAVG STD_DEV : %0.2f Gb/s %0.2f Gb/s\n", min*KOEF, max*KOEF, avg*KOEF, std_dev*KOEF)};

                `uvm_info(this.get_full_name(), msg, UVM_LOW);
                speed.reset();
                data_size.reset();
                sections_it = 0;
                start_time  = stop_time;
            end
        end
    endtask

endclass
