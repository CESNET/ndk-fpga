// statistics.sv: Statistics of transaction flows
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class statistics extends uvm_subscriber #(sequence_item);
    `uvm_component_utils(uvm_lbus::statistics);

    // ---------- //
    // Parameters //
    // ---------- //

    int unsigned measures = 100;

    // --------- //
    // Variables //
    // --------- //

    protected uvm_common::stats stats;
    protected int unsigned      data;
    protected bit               inside_frame;
    protected int unsigned      ready_deassertion_counter;

    // Constructor
    function new(string name = "statistics", uvm_component parent = null);
        super.new(name, parent);

        stats                     = new();
        data                      = 0;
        inside_frame              = 0;
        ready_deassertion_counter = 0;
    endfunction

    function void write(sequence_item t);
        int unsigned data_size = 0;

        // Up to four write cycles might be safely performed after tx_rdyout is negated, but no more until tx_rdyout is asserted again.
        // https://docs.amd.com/v/u/2.4-English/pg203-cmac-usplus: Chapter 3: Designing with the Core
        if (t.rdy !== 1'b1) begin
            if (ready_deassertion_counter > 4) begin
                return;
            end
            ready_deassertion_counter++;
        end
        else begin
            ready_deassertion_counter = 0;
        end

        for (int unsigned i = 0; i < 4; i++) begin
            if (t.ena[i] !== 1'b1) begin // Skip an invalid segment
                continue;
            end

            if (!inside_frame) begin
                if (t.sop[i] === 1'b1 && t.eop[i] === 1'b1) begin
                    data_size += 128 - 8*t.mty[4*(i+1)-1 -: 4];
                end
                else if (t.sop[i] === 1'b1) begin
                    inside_frame = 1;
                    data_size += 128;
                end
                else begin
                    assert(t.eop[i] !== 1'b1)
                    else begin
                       `uvm_error(this.get_full_name(), "\n\tThe EOP was set before a new packet transfer started. A SOP wasn't set before this EOP")
                    end
                end
            end
            else begin
                if (t.eop[i] === 1'b1) begin
                    inside_frame = 0;
                    data_size += 128 - 8*t.mty[4*(i+1)-1 -: 4];
                end
                else begin
                    data_size += 128;
                end

                assert(t.sop[i] !== 1'b1)
                else begin
                    `uvm_error(this.get_full_name(), "\n\tThe SOP was before the last packet transfer correctly ended. A EOP wasn't set at the end of the packet transfer")
                end
            end
        end

        data += data_size;
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
                stats.next_val(real'(data)/((step_end_time-step_start_time)/1ns));

                data = 0;
            end

            begin
                string msg;
                real min, max, avg, std_dev;

                start_time = end_time;
                end_time   = step_end_time;

                stats.count(min, max, avg, std_dev);
                msg = $sformatf("\n\tData Speed [%0dns:%0dns]\n\t\tAverage : %0.2fGb/s std_dev %0.2fGb/s\n\t\tmin : %0.2fGb/s max  %0.2fGb/s",
                        start_time/1ns, end_time/1ns, avg, std_dev, min, max);

                `uvm_info(this.get_full_name(), msg, UVM_LOW);

                stats.reset();
            end
        end
    endtask

endclass
