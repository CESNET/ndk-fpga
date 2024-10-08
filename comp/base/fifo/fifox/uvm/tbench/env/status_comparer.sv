// status_comparer.sv: Ordered comparer without check phase
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class status_comparer #(int unsigned STATUS_WIDTH) extends uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(STATUS_WIDTH+2));
    `uvm_component_param_utils(uvm_fifox::status_comparer #(STATUS_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction


    function string model_item2string(uvm_logic_vector::sequence_item #(STATUS_WIDTH+2) tr);
        logic [STATUS_WIDTH-1:0] status;
        logic afull;
        logic aempty;

        { status, afull, aempty } = tr.data;

        return $sformatf("\nStatus\n%s\n\tITEMS %0d\n\tAlmoust full %b\n\tAlmoust full %b", tr.time2string(), status, afull, aempty);
    endfunction

    function string dut_item2string(uvm_logic_vector::sequence_item #(STATUS_WIDTH+2) tr);
        logic [STATUS_WIDTH-1:0] status;
        logic afull;
        logic aempty;

        { status, afull, aempty } = tr.data;

        return $sformatf("\nStatus\n%s\n\tITEMS %0d\n\tAlmoust full %b\n\tAlmoust full %b", tr.time2string(), status, afull, aempty);
    endfunction

    function void check_phase(uvm_phase phase);
        flush();
    endfunction

endclass
