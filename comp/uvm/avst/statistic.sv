//-- statistic.sv :
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class statistic #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_subscriber#(sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH));
    `uvm_component_param_utils(uvm_avst::statistic#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH));


    // SPEED mesures
    protected uvm_common::stats speed;
    protected int unsigned      speed_data;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        speed_data     = 0;
        speed          = new();
    endfunction

    function void write(sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) t);
        int unsigned data_size = 0;

        for (int unsigned it = 0; it < REGIONS; it++) begin
            if (t.valid[it]) begin
                data_size += REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;

                if (t.eop[it]) begin
                    data_size -= t.empty[it]*ITEM_WIDTH;
                end
            speed_data += data_size;
            end
        end
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

                #(10us);
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

