// monitor.sv: pcie monitor
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class sequence_data  extends uvm_sequence#(
    uvm_logic_vector_array::sequence_item #(32)
);
    `ndk_object_utils(uvm_pcie_mfb::sequence_data);

    uvm_common::fifo#(uvm_logic_vector_array::sequence_item #(32))            fifo;


    function new(string name = "uvm_pcie_mfb::sequence_simple");
        super.new(name);
    endfunction


    task body;
        // verilog_lint: waive line-length
        uvm_config_db #(uvm_common::fifo #(uvm_logic_vector_array::sequence_item #(32)))::get(m_sequencer, "", "in_fifo",
                                                                                           fifo);

        forever begin
            fifo.get(req);
            start_item(req);
            finish_item(req);
        end
    endtask
endclass


class sequence_meta#(
    direction_t  DIR,
    device_t     DEVICE
) extends uvm_sequence#(
    uvm_logic_vector::sequence_item #(meta_width_get(DIR, DEVICE))
);
    `ndk_object_param_utils(
        uvm_pcie_mfb::sequence_meta#(DIR, DEVICE),
        $sformatf("uvm_pcie_mfb::sequence_meta#(%s,%s)",DIR, DEVICE)
    );

    uvm_common::fifo#(uvm_logic_vector::sequence_item #(meta_width_get(DIR, DEVICE))) fifo;

    function new(string name = "uvm_pcie_mfb::sequence_simple");
        super.new(name);
    endfunction

    task body;
        // verilog_lint: waive line-length
        uvm_config_db#(uvm_common::fifo#(uvm_logic_vector::sequence_item #(meta_width_get(DIR, DEVICE))))::get(m_sequencer, "" , "in_fifo", fifo);

        forever begin
            fifo.get(req);
            start_item(req);
            finish_item(req);
        end
    endtask
endclass


