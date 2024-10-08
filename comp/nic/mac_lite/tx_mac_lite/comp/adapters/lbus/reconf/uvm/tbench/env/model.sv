// model.sv: Model of implementation
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Vladislav Valek <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class model extends uvm_component;
    `uvm_component_param_utils(uvm_mfb_to_lbus_adapter::model)

    uvm_tlm_analysis_fifo #(uvm_byte_array::sequence_item)   input_data;
    uvm_analysis_port #(uvm_byte_array::sequence_item)       out_data;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        input_data    = new("input_data", this);
        out_data      = new("out_data", this);

    endfunction


    task run_phase(uvm_phase phase);

        uvm_byte_array::sequence_item tr_input_packet;

        forever begin

            input_data.get(tr_input_packet);
            out_data.write(tr_input_packet);

        end

    endtask
endclass
