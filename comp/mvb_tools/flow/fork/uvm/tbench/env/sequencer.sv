// sequencer.sv: Virtual sequencer
// MVB_FORK UVM verification
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer#(ITEM_WIDTH, OUTPUT_PORTS) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mvb_fork::virt_sequencer#(ITEM_WIDTH, OUTPUT_PORTS))

    uvm_reset::sequencer                     m_reset;
    uvm_logic_vector::sequencer#(ITEM_WIDTH) m_logic_vector_scr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
