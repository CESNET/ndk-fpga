// monitor.sv: Monitors for the converting environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class monitor_logic_vector_array extends uvm_logic_vector_array::monitor #(8);
    `uvm_component_utils(uvm_logic_vector_array_lbus::monitor_logic_vector_array)

    localparam int unsigned READY_DEASSERTION_DELAY = 4;

    // Reset
    uvm_reset::sync_terminate reset_sync;

    // Analysis export
    uvm_analysis_imp #(uvm_lbus::sequence_item, monitor_logic_vector_array) analysis_export;

    // ------------------ //
    // Internal variables //
    // ------------------ //

    protected bit inside_frame;
    protected logic [8-1 : 0] bytes[$];
    protected int unsigned ready_deassertion_counter;

    function new(string name = "monitor_logic_vector_array", uvm_component parent = null);
        super.new(name, parent);

        reset_sync = new();
        analysis_export = new("analysis_export", this);

        inside_frame = 0;
        ready_deassertion_counter = 0;
    endfunction

    protected virtual function void save_segment(logic [128-1 : 0] data, logic [4-1 : 0] mty = 0);
        for (int unsigned i = (128/8); i > mty; ) begin
            i--;
            bytes.push_back(data[8*(i+1)-1 -: 8]);
        end
    endfunction

    protected virtual function void send_packet();
        uvm_logic_vector_array::sequence_item #(8) item;

        item = uvm_logic_vector_array::sequence_item #(8)::type_id::create("item");
        item.data = bytes;
        bytes.delete();
        analysis_port.write(item);
    endfunction

    function void write(uvm_lbus::sequence_item t);
        if (reset_sync.has_been_reset()) begin
            inside_frame = 0;
            ready_deassertion_counter = 0;
            bytes.delete();
        end

        // Up to four write cycles might be safely performed after tx_rdyout is negated, but no more until tx_rdyout is asserted again.
        // https://docs.amd.com/v/u/2.4-English/pg203-cmac-usplus: Chapter 3: Designing with the Core
        if (t.rdy !== 1'b1) begin
            if (ready_deassertion_counter > READY_DEASSERTION_DELAY) begin
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
                    save_segment(t.data[128*(i+1)-1 -: 128], t.mty[4*(i+1)-1 -: 4]);
                end
                else if (t.sop[i] === 1'b1) begin
                    inside_frame = 1;
                    save_segment(t.data[128*(i+1)-1 -: 128], 0);
                end
                else begin
                    assert(t.eop[i] !== 1'b1)
                    else begin
                        string msg;
                        // verilog_lint: waive line-length
                        msg = "\n\tThe EOP was set before a new packet transfer started. A SOP wasn't set before this EOP";
                       `uvm_error(this.get_full_name(), msg);
                    end
                end
            end
            else begin
                if (t.eop[i] === 1'b1) begin
                    inside_frame = 0;
                    save_segment(t.data[128*(i+1)-1 -: 128], t.mty[4*(i+1)-1 -: 4]);
                    send_packet();
                end
                else begin
                    save_segment(t.data[128*(i+1)-1 -: 128], 0);
                end

                assert(t.sop[i] !== 1'b1)
                else begin
                    string msg;
                    // verilog_lint: waive line-length
                    msg = "\n\tThe SOP was before the last packet transfer correctly ended. A EOP wasn't set at the end of the packet transfer";
                    `uvm_error(this.get_full_name(), msg);
                end
            end
        end
    endfunction

endclass

class monitor_logic_vector extends uvm_logic_vector::monitor #(1);
    `uvm_component_utils(uvm_logic_vector_array_lbus::monitor_logic_vector)

    localparam int unsigned READY_DEASSERTION_DELAY = 4;

    // Reset
    uvm_reset::sync_terminate reset_sync;
    // Analysis export
    uvm_analysis_imp #(uvm_lbus::sequence_item, monitor_logic_vector) analysis_export;

    // ------------------ //
    // Internal variables //
    // ------------------ //

    protected int unsigned ready_deassertion_counter;

    function new (string name, uvm_component parent);
        super.new(name, parent);

        reset_sync = new();
        analysis_export = new("analysis_export", this);

        ready_deassertion_counter = 0;
    endfunction

    virtual function void write(uvm_lbus::sequence_item t);
        if (reset_sync.has_been_reset()) begin
            ready_deassertion_counter = 0;
        end

        // Up to four write cycles might be safely performed after tx_rdyout is negated, but no more until tx_rdyout is asserted again.
        // https://docs.amd.com/v/u/2.4-English/pg203-cmac-usplus: Chapter 3: Designing with the Core
        if (t.rdy !== 1'b1) begin
            if (ready_deassertion_counter > READY_DEASSERTION_DELAY) begin
                return;
            end
            ready_deassertion_counter++;
        end
        else begin
            ready_deassertion_counter = 0;
        end

        for (int unsigned i = 0; i < 4; i++) begin
            if (t.ena[i] === 1'b1 && t.eop[i] === 1'b1) begin
                uvm_logic_vector::sequence_item #(1) item;

                item = uvm_logic_vector::sequence_item #(1)::type_id::create("item");
                item.data = t.err[i];
                analysis_port.write(item);
            end
        end
    endfunction

endclass
