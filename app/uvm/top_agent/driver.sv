/*
 * file       : agent.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: top_agent
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class driver extends uvm_driver #(uvm_byte_array::sequence_item);
    // registration of component tools
    `uvm_component_utils(top_agent::driver)

    //RESET reset_sync
    uvm_reset::sync_terminate reset_sync;

    uvm_byte_array::sequence_item m_sequencer;
    //uvm_seq_item_pull_imp #( byte_array::sequence_item, byte_array::sequence_item , driver) byte_array_export;
    mailbox#(uvm_byte_array::sequence_item) byte_array_export;
    mailbox#(uvm_byte_array::sequence_item) header_export;

    // Contructor, where analysis port is created.
    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        byte_array_export = new(10);
        header_export     = new(10);
        reset_sync = new();
    endfunction: new

    // -----------------------
    // Functions.
    // -----------------------

    task run_phase(uvm_phase phase);
        uvm_byte_array::sequence_item clone_item;

        forever begin
            // Get new sequence item to drive to interface
            wait((byte_array_export.num() < 10 &&  header_export.num() < 10) || reset_sync.is_reset());
            if (reset_sync.has_been_reset()) begin
                uvm_byte_array::sequence_item tmp;

                while (byte_array_export.try_get(tmp)) begin
                end

                while (header_export.try_get(tmp)) begin
                end

                while(reset_sync.has_been_reset() != 0) begin
                    #(40ns);
                end
            end

            seq_item_port.get_next_item(req);
            $cast(clone_item, req.clone());
            byte_array_export.put(clone_item);
            header_export.put(clone_item);
            seq_item_port.item_done();
        end
    endtask
endclass

