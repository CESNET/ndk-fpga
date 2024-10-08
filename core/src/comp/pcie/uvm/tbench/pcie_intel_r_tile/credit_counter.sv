// credit_counter.sv: Counter of AVST credit
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class credit_counter extends uvm_subscriber #(credit_item);
    `uvm_component_utils(uvm_pcie_intel_r_tile::credit_counter)

    // --------- //
    // Variables //
    // --------- //

    typedef enum {
        IDLE,
        INITIALIZING,
        INIT_DONE
    } state_e;

    protected state_e state;
    protected logic infinite_credits;
    protected int unsigned count;

    // Constructor
    function new(string name = "credit_counter", uvm_component parent = null);
        super.new(name, parent);

        state            = IDLE;
        infinite_credits = 0;
        count            = 0;
    endfunction

    function void write(credit_item t);
        if (t.init === 1'b1 && t.init_ack === 1'b1) begin // Start of initialization
            state            = INITIALIZING;
            infinite_credits = 0;
            count            = 0;
        end
        else if (state == INITIALIZING && t.init === 1'b0) begin // End of initialization
            state = INIT_DONE;
            // 0 credits => inifinite credits
            if (count == 0) begin
                infinite_credits = 1;
            end
        end

        if (state == INITIALIZING || state == INIT_DONE) begin
            if (t.update === 1'b1 && !infinite_credits) begin
                count += t.update_cnt;
            end
        end
    endfunction

    function logic is_init_done();
        return (state == INIT_DONE);
    endfunction

    task wait_for_init_done();
        wait(state == INIT_DONE);
    endtask

    task reduce(int unsigned cost);
        if (infinite_credits) begin
            return;
        end

        wait(count >= cost);
        count -= cost;
    endtask

    function logic is_enough(int unsigned cost);
        if (infinite_credits) begin
            return 1;
        end

        return (count >= cost);
    endfunction

    function logic try_reduce(int unsigned cost);
        if (infinite_credits) begin
            return 1;
        end

        if (is_enough(cost)) begin
            count -= cost;
            return 1;
        end

        return 0;
    endfunction

endclass
