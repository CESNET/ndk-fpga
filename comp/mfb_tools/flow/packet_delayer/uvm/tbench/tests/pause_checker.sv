// pause_checker.sv: PAUSE_REQUEST edge checker
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

// Verifies that the RX FIFO almost-full/almost-empty mechanism toggles the DUT
// PAUSE_REQUEST output: a RISE proves the FIFO reached FIFO_AFULL, a FALL
// proves it drained back to FIFO_AEMPTY. Both edges are required.
//
// The check runs in check_phase (before report_phase), so its errors are
// counted in the scoreboard's final verdict.
class pause_checker extends uvm_component;
    `uvm_component_utils(test::pause_checker)

    virtual pause_if vif;

    int unsigned n_rise       = 0;
    int unsigned n_fall       = 0;
    time         t_first_rise = 0;
    time         t_first_fall = 0;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        if (!uvm_config_db#(virtual pause_if)::get(this, "", "vif_pause", vif)) begin
            `uvm_fatal(get_type_name(), "No virtual pause_if (config DB key \"vif_pause\")")
        end
    endfunction

    task run_phase(uvm_phase phase);
        // bit, not logic: an initial X -> 0 must not count as a falling edge
        bit prev = 1'b0;

        forever begin
            @(posedge vif.CLK);
            if ((vif.PAUSE_REQUEST === 1'b1) && (prev !== 1'b1)) begin
                if (n_rise++ == 0) begin
                    t_first_rise = $time;
                    `uvm_info(get_type_name(), $sformatf("PAUSE_REQUEST RISE at %0t: RX FIFO reached FIFO_AFULL",
                              $time), UVM_LOW)
                end
            // A fall only counts after a rise (it proves the FIFO drained after AFULL)
            end else if ((vif.PAUSE_REQUEST === 1'b0) && (prev !== 1'b0) && (n_rise != 0)) begin
                if (n_fall++ == 0) begin
                    t_first_fall = $time;
                    `uvm_info(get_type_name(), $sformatf("PAUSE_REQUEST FALL at %0t: RX FIFO reached FIFO_AEMPTY",
                              $time), UVM_LOW)
                end
            end
            prev = vif.PAUSE_REQUEST;
        end
    endtask

    // Poll (with timeout) until a falling edge has been observed
    task wait_fall(time timeout, output bit ok);
        time t0 = $time;
        while ((n_fall == 0) && (($time - t0) < timeout)) begin
            #(1ns);
        end
        ok = (n_fall != 0);
    endtask

    function void check_phase(uvm_phase phase);
        if (n_rise == 0) begin
            `uvm_error(get_type_name(),
                       "PAUSE_REQUEST never rose: the RX FIFO did NOT reach almost-full (FIFO_AFULL untested)")
        end
        if (n_fall == 0) begin
            `uvm_error(get_type_name(),
                       "PAUSE_REQUEST never fell: the RX FIFO did NOT drain to almost-empty (FIFO_AEMPTY untested)")
        end
    endfunction

    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), $sformatf(
                  "\n\tPAUSE_REQUEST summary:\n\t  rises %0d (first %0t)\n\t  falls %0d (first %0t)",
                  n_rise, t_first_rise, n_fall, t_first_fall), UVM_LOW)
    endfunction
endclass
