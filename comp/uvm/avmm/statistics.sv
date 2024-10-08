// statistics.sv: Statistics of transaction flows
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class statistics #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_avmm::statistics #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH));

    // --------- //
    // Variables //
    // --------- //

    int unsigned measures = 10;

    protected uvm_common::stats read_stats;
    protected uvm_common::stats write_stats;
    protected int unsigned      read_data;
    protected int unsigned      write_data;

    // ----------- //
    // Input ports //
    // ----------- //

    `uvm_analysis_imp_decl(_slave)
    `uvm_analysis_imp_decl(_master)

    typedef statistics #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) this_type;
    uvm_analysis_imp_slave  #(sequence_item_response #(DATA_WIDTH), this_type)                            analysis_export_slave;
    uvm_analysis_imp_master #(sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH), this_type) analysis_export_master;

    // Constructor
    function new(string name = "statistics", uvm_component parent = null);
        super.new(name, parent);

        analysis_export_slave  = new("analysis_export_slave", this);
        analysis_export_master = new("analysis_export_master", this);

        read_stats  = new();
        write_stats = new();
        read_data   = 0;
        write_data  = 0;
    endfunction

    // Response item
    function void write_slave(sequence_item_response #(DATA_WIDTH) t);
        if (t.readdatavalid === 1'b1) begin
            read_data += DATA_WIDTH;
        end
    endfunction

    // Request item
    function void write_master(sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) t);
        if (t.ready === 1'b1 && t.write === 1'b1) begin
            write_data += DATA_WIDTH;
        end
    endfunction

    task run_phase(uvm_phase phase);
        time start_time;
        time end_time = $time;

        forever begin
            time step_start_time;
            time step_end_time = end_time;

            for (int unsigned m = 0; m < measures; m++) begin
                step_start_time = step_end_time;

                #(1us);
                step_end_time = $time;
                read_stats .next_val(real'(read_data)/((step_end_time-step_start_time)/1ns));
                write_stats.next_val(real'(write_data)/((step_end_time-step_start_time)/1ns));

                read_data  = 0;
                write_data = 0;
            end

            begin
                string read_msg;
                string write_msg;
                real min, max, avg, std_dev;

                start_time = end_time;
                end_time   = step_end_time;

                read_stats.count(min, max, avg, std_dev);
                read_msg = $sformatf("\n\tResponse Read Data Speed [%0dns:%0dns]\n\t\tAverage : %0.2fGb/s std_dev %0.2fGb/s\n\t\tmin : %0.2fGb/s max  %0.2fGb/s",
                        start_time/1ns, end_time/1ns, avg, std_dev, min, max);

                write_stats.count(min, max, avg, std_dev);
                write_msg = $sformatf("\n\tRequest Write Data Speed [%0dns:%0dns]\n\t\tAverage : %0.2fGb/s std_dev %0.2fGb/s\n\t\tmin : %0.2fGb/s max  %0.2fGb/s",
                        start_time/1ns, end_time/1ns, avg, std_dev, min, max);

                `uvm_info(this.get_full_name(), { read_msg, "\n", write_msg }, UVM_LOW);

                read_stats.reset();
                write_stats.reset();
            end
        end
    endtask

endclass
