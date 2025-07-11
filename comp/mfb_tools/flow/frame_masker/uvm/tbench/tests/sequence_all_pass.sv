// sequence_all_pass.sv: Sequence with masking off
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class sequence_all_pass #(int unsigned MFB_REGIONS) extends uvm_logic_vector::sequence_endless #(MFB_REGIONS);
    `uvm_object_param_utils(test::sequence_all_pass #(MFB_REGIONS))

    // Constructor
    function new(string name = "sequence_all_pass");
        super.new(name);
    endfunction

    task body;
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        while(state == null || state.next()) begin
            `uvm_do_with(req, {
                req.data == { MFB_REGIONS { 1'b1 } }; // Doesn't discard
            })
        end
    endtask

endclass
