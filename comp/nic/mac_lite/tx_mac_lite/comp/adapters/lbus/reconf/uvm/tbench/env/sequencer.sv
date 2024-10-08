// sequencer.sv: Virtual sequencer
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Vladislav Valek <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mfb_to_lbus_adapter::virt_sequencer)

    uvm_reset::sequencer        m_reset;
    uvm_byte_array::sequencer   m_byte_array_scr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
