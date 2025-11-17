//-- sequence.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// This low level sequence define bus functionality
class logic_vector_array_sequence #(
    int unsigned ITEM_WIDTH
) extends uvm_sequence #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH));

    `uvm_object_param_utils(uvm_dma_ll_rx::logic_vector_array_sequence #(ITEM_WIDTH))

    mailbox#(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)) tr_export;

    function new(string name = "sequence_simple_rx_base");
        super.new(name);
    endfunction

    task body;

        req = uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)::type_id::create("req", this.m_sequencer);
        forever begin
            uvm_logic_vector_array::sequence_item #(ITEM_WIDTH) hl_tr;

            // Sequence download data from higher level driver and
            // send them to lower lever driver. Download data only when
            // data is available and low lever driver is prepared.
            wait(tr_export.num() != 0);
            start_item(req);
            tr_export.get(hl_tr);
            req.copy(hl_tr);
            finish_item(req);
        end
    endtask
endclass



class logic_vector_sequence #(
    int unsigned META_WIDTH
) extends uvm_sequence #(uvm_logic_vector::sequence_item #(META_WIDTH));

    `uvm_object_param_utils(uvm_dma_ll_rx::logic_vector_sequence #(META_WIDTH))

    mailbox#(uvm_logic_vector::sequence_item #(META_WIDTH)) tr_export;

    function new(string name = "sequence_simple_rx_base");
        super.new(name);
    endfunction

    task body;

        req = uvm_logic_vector::sequence_item #(META_WIDTH)::type_id::create("req", this.m_sequencer);
        forever begin
            uvm_logic_vector::sequence_item #(META_WIDTH) hl_tr;

            // Sequence download data from higher level driver and
            // send them to lower lever driver. Download data only when
            // data is available and low lever driver is prepared.
            wait(tr_export.num() != 0);
            start_item(req);
            tr_export.get(hl_tr);
            req.copy(hl_tr);
            finish_item(req);
        end
    endtask
endclass

