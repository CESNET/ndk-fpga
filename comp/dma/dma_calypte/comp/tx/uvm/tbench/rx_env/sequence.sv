// sequence.sv: Low-level sequence that defines bus functionality
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class base_send_sequence #(type T_ITEM) extends uvm_sequence #(T_ITEM);
    `uvm_object_param_utils(uvm_tx_dma_calypte_cq::base_send_sequence #(T_ITEM))

    mailbox #(T_ITEM) m_tr_export;

    function new(string name = "base_send_sequence");
        super.new(name);
    endfunction

    task body;
        forever begin
            m_tr_export.get(req);
            start_item(req);
            finish_item(req);
        end
    endtask
endclass

