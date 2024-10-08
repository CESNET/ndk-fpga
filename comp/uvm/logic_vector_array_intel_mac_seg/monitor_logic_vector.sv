/*
 * file       : monitor.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: converting Intel mac seq into byte array
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class monitor_logic_vector #(int unsigned WIDTH, int unsigned SEGMENTS) extends uvm_logic_vector::monitor #(WIDTH);
    `uvm_component_param_utils(uvm_logic_vector_array_intel_mac_seg::monitor_logic_vector#(WIDTH, SEGMENTS))

    uvm_analysis_imp #(uvm_intel_mac_seg::sequence_item #(SEGMENTS), monitor_logic_vector#(WIDTH, SEGMENTS)) analysis_export;
    uvm_logic_vector::sequence_item#(WIDTH) hl_tr;
    uvm_reset::sync_terminate reset_sync;

    typedef enum {FRAME, NO_FRAME} state_t;
    state_t state;
    byte unsigned data[$];

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
        state = NO_FRAME;
        reset_sync = new();
    endfunction

    virtual function void write(uvm_intel_mac_seg::sequence_item #(SEGMENTS) tr);
        //check if in past has been set reset
        if (reset_sync.has_been_reset()) begin
            state = NO_FRAME;
        end

        if (tr.valid !== 1 || reset_sync.is_reset() == 1) begin
            return;
        end

        for (int unsigned it = 0; it < SEGMENTS; it++) begin
            //detection start of packet
            if (state == NO_FRAME && tr.inframe[it] == 1) begin
                state = FRAME;
            end

            //detection eof
            if (state == FRAME && tr.inframe[it] == 0) begin
                state = NO_FRAME;
                hl_tr = uvm_logic_vector::sequence_item#(WIDTH)::type_id::create("hl_tr", this);
                hl_tr.data = {tr.fcs_error[it], tr.error[it], tr.status_data[it]};
                hl_tr.start[this.get_full_name()] = $time();
                analysis_port.write(hl_tr);
            end
        end
    endfunction

endclass

