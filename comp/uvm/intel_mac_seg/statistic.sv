//-- statistic.sv :
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class statistic#(SEGMENTS) extends uvm_subscriber#(sequence_item #(SEGMENTS));
    `uvm_component_param_utils(uvm_intel_mac_seg::statistic#(SEGMENTS));


    // SPEED mesures
    protected uvm_common::stats speed;
    protected int unsigned      speed_data;
    protected logic             indata;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        speed_data     = 0;
        indata         = 0;
        speed          = new();
    endfunction

    function void write(sequence_item #(SEGMENTS) t);
        int unsigned data_size = 0;

        if (t.valid == 1'b1) begin
            for (int unsigned it = 0; it < SEGMENTS; it++) begin
                if (t.inframe[it] === 1'b1) begin
                    data_size += 64;
                    indata = 1;
                end else if (indata == 1) begin
                    data_size += 64 - t.eop_empty[it] *8;
                    indata = 0;
                end
            end
        end

        speed_data += data_size;
    endfunction

    task run_phase(uvm_phase phase);
        time speed_start_time;
        time speed_end_time;
        const int unsigned mesures = 100;
        string msg;

        speed_end_time = 0ns;
        forever begin
            time step_speed_end_time = speed_end_time;
            time step_speed_start_time;

            for (int unsigned it = 0; it < mesures; it++) begin
                step_speed_start_time = step_speed_end_time;

                #(1us);
                step_speed_end_time = $time();
                //if (speed_data == 0) begin
                //    $write("SPEED 0\n\t%s\n\t%0dns %0dns\n",this.get_full_name(), speed_start_time/1ns, speed_end_time/1ns);
                //end
                speed.next_val(real'(speed_data)/((step_speed_end_time-step_speed_start_time)/1ns));

                speed_data = 0;
            end

            begin
                real min, max, avg, std_dev;

                speed_start_time = speed_end_time;
                speed_end_time   = step_speed_end_time;
                speed.count(min, max, avg, std_dev);
                msg = $sformatf("\n\tSpeed [%0dns:%0dns]\n\t\tAverage : %0.2fGb/s std_dev %0.2fGb/s\n\t\tmin : %0.2fGb/s max  %0.2fGb/s",
                        speed_start_time/1ns, speed_end_time/1ns, avg, std_dev, min, max);
                `uvm_info(this.get_full_name(), msg, UVM_LOW);
                speed.reset();
            end
        end
    endtask
endclass

