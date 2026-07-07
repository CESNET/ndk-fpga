// timestamp_checker.sv: Checks the validity of the DUT timestamps
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class timestamp_checker #(int unsigned DUT_ITEM_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_network_mod_env::timestamp_checker #(DUT_ITEM_WIDTH));

    // ------ //
    // Inputs //
    // ------ //

    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(64))             in_model;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(DUT_ITEM_WIDTH)) in_dut;

    // ------------------ //
    // Internal variables //
    // ------------------ //

    bit              waiting_for_model_item;
    int unsigned     dut_timestamp_counter;
    longint unsigned previous_dut_timestamp;

    // Constructor
    function new(string name = "timestamp_checker", uvm_component parent = null);
        super.new(name, parent);

        in_model = new("in_model", this);
        in_dut   = new("in_dut", this);

        waiting_for_model_item = 0;
        dut_timestamp_counter  = 0;
        previous_dut_timestamp = 0;
    endfunction

    task run_phase(uvm_phase phase);
        uvm_logic_vector::sequence_item #(64)             model_item;
        uvm_logic_vector::sequence_item #(DUT_ITEM_WIDTH) dut_item;
        bit                                               dut_timestamp_valid;
        longint unsigned                                  dut_timestamp;

        forever begin
            in_dut.get(dut_item);
            dut_timestamp_counter++;

            dut_timestamp       = dut_item.data[DUT_ITEM_WIDTH   -1 -: 64];
            dut_timestamp_valid = dut_item.data[DUT_ITEM_WIDTH-64-1 -: 1];

            // Skip invalid timestamps
            if (dut_timestamp_valid !== 1'b1) begin
                continue;
            end

            // Check that the timestamp value does not decrease over time
            if (dut_timestamp < previous_dut_timestamp) begin
                `uvm_error(get_full_name(),
                           $sformatf(
                               "\n\tThe timestamp value must not decrease over time. Current: 0x%0h, Previous: 0x%0h",
                               dut_timestamp, previous_dut_timestamp))
            end

            // The timestamp obtained from the DUT may be duplicated
            if (dut_timestamp == previous_dut_timestamp) begin
                continue;
            end

            // Try to find the next matching model timestamp
            do begin
                waiting_for_model_item = 1;
                in_model.get(model_item);
                waiting_for_model_item = 0;

                if (dut_timestamp < model_item.data) begin
                    `uvm_error(
                        get_full_name(), $sformatf(
                        "\n\tThe timestamp (#%0d) obtained from the DUT has an unknown origin", dut_timestamp_counter));
                end
            end while (dut_timestamp > model_item.data);

            previous_dut_timestamp = dut_timestamp;
        end
    endtask

    function bit success();
        return (waiting_for_model_item == 0); // Check if the call `in_model.get(model_item)` is not blocked
    endfunction

    function void check_phase(uvm_phase phase);
        super.check_phase(phase);

        assert(this.success())
        else begin
            `uvm_error(get_full_name(), $sformatf(
                       "\n\tThe timestamp (#%0d) obtained from the DUT has an unknown origin", dut_timestamp_counter));
        end
    endfunction

endclass
