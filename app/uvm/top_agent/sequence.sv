/*
 * file       : sequence.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description:  top agent
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class byte_array_sequence_simple extends uvm_sequence #(byte_array::sequence_item);
    `uvm_object_utils(top_agent::byte_array_sequence_simple)
    `uvm_declare_p_sequencer(byte_array::sequencer);

    mailbox#(byte_array::sequence_item) packet_export;

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------
    task body;
        req = byte_array::sequence_item::type_id::create("req", p_sequencer);
        if(!uvm_config_db#(mailbox#(byte_array::sequence_item))::get(p_sequencer, "", "packet_export", packet_export)) begin
            `uvm_fatal(p_sequencer.get_full_name(), "\n\tFailed to get packet msg box");
        end
        forever begin
            byte_array::sequence_item tmp_packet;
            packet_export.get(tmp_packet);
            start_item(req);
            req.copy(tmp_packet);
            finish_item(req);
        end
    endtask

endclass


class mvb_config;
    int unsigned port_max = 16;
    int unsigned port_min = 0;
endclass

class mvb_sequence_simple_eth #(ITEMS, ITEM_WIDTH) extends uvm_sequence #(mvb::sequence_item #(ITEMS, ITEM_WIDTH));
    `uvm_object_param_utils(top_agent::mvb_sequence_simple_eth  #(ITEMS, ITEM_WIDTH))
    `uvm_declare_p_sequencer(mvb::sequencer#(ITEMS, ITEM_WIDTH));

    mailbox#(byte_array::sequence_item) header_export;

    // ------------------------------------------------------------------------
    // Variables
    int unsigned transaction_count_max = 2048;
    int unsigned transaction_count_min = 32;
    rand int unsigned transaction_count;
    mvb_config   m_config;

    constraint tr_cnt_cons {transaction_count inside {[transaction_count_min:transaction_count_max]};}

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "Simple sequence rx");
        super.new(name);
    endfunction

    // ------------------------------------------------------------------------
    // Generates transactions
    task body();
        logic reset;
        // Generate transaction_count transactions
        req = mvb::sequence_item #(ITEMS, ITEM_WIDTH)::type_id::create("req", p_sequencer);
        if(!uvm_config_db#(mailbox#(byte_array::sequence_item))::get(p_sequencer, "", "hdr_export", header_export)) begin
            `uvm_fatal(p_sequencer.get_full_name(), "\n\tFailed to get packet msg box");
        end

        if(!uvm_config_db#(mvb_config)::get(p_sequencer, "", "m_config", m_config)) begin
            `uvm_fatal(p_sequencer.get_full_name(), "\n\tFailed to get mvb_config");
        end

        repeat(transaction_count) begin
            // Create a request for sequence item
            $timeformat(-9, 2, " ns", 20);
            start_item(req);

            // Do not generate new data when SRC_RDY was 1 but the transaction does not transfare;
            if (!req.randomize() with {SRC_RDY == 1'b1 -> $countones(VLD) <= header_export.num(); header_export.num() == 0 -> SRC_RDY == 1'b0;
                                       foreach(DATA[it]) { DATA[it][24-1:16] inside {[m_config.port_min:m_config.port_max]}; }}) begin
                `uvm_fatal(p_sequencer.get_full_name(), "\n\tSequence faile to randomize transaction.")
            end
            if (req.SRC_RDY == 1'b1) begin
                for (int unsigned it = 0; it < ITEMS; it++) begin
                    if (req.VLD[it] == 1'b1) begin
                        byte_array::sequence_item tmp_packet;
                        header_export.get(tmp_packet);
                        req.DATA[it][16-1:0] = tmp_packet.size();
                    end
                end
            end
            finish_item(req);

            // Get response from driver
            get_response(rsp);

            reset = p_sequencer.reset_sync.has_been_reset();
            while (rsp.SRC_RDY != 0 && !rsp.DST_RDY && !reset) begin
                start_item(req);
                finish_item(req);
                get_response(rsp);
            end
        end
    endtask
endclass

class mvb_sequence_lib_eth #(ITEMS, ITEM_WIDTH) extends uvm_sequence_library#(mvb::sequence_item#(ITEMS, ITEM_WIDTH));
  `uvm_object_param_utils(top_agent::mvb_sequence_lib_eth #(ITEMS, ITEM_WIDTH))
  `uvm_sequence_library_utils(top_agent::mvb_sequence_lib_eth#(ITEMS, ITEM_WIDTH))

    function new(string name = "");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence();
        this.add_sequence(mvb_sequence_simple_eth #(ITEMS, ITEM_WIDTH)::get_type());
    endfunction
endclass

class mvb_sequence_simple #(ITEMS, ITEM_WIDTH) extends uvm_sequence #(mvb::sequence_item #(ITEMS, ITEM_WIDTH));
    `uvm_object_param_utils(top_agent::mvb_sequence_simple #(ITEMS, ITEM_WIDTH))
    `uvm_declare_p_sequencer(mvb::sequencer#(ITEMS, ITEM_WIDTH));

    mailbox#(byte_array::sequence_item) header_export;

    // ------------------------------------------------------------------------
    // Variables
    int unsigned transaction_count_max = 2048;
    int unsigned transaction_count_min = 32;
    rand int unsigned transaction_count;

    constraint tr_cnt_cons {transaction_count inside {[transaction_count_min:transaction_count_max]};}

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "Simple sequence rx");
        super.new(name);
    endfunction

    // ------------------------------------------------------------------------
    // Generates transactions
    task body();
        logic reset;
        // Generate transaction_count transactions
        req = mvb::sequence_item #(ITEMS, ITEM_WIDTH)::type_id::create("req", p_sequencer);
        if(!uvm_config_db#(mailbox#(byte_array::sequence_item))::get(p_sequencer, "", "hdr_export", header_export)) begin
            `uvm_fatal(p_sequencer.get_full_name(), "\n\tFailed to get packet msg box");
        end

        repeat(transaction_count) begin
            // Create a request for sequence item
            $timeformat(-9, 2, " ns", 20);
            start_item(req);

            // Do not generate new data when SRC_RDY was 1 but the transaction does not transfare;
            if (!req.randomize() with {SRC_RDY == 1'b1 -> $countones(VLD) <= header_export.num();  header_export.num() == 0 -> SRC_RDY == 1'b0;}) begin
                `uvm_fatal(p_sequencer.get_full_name(), "\n\tSequence faile to randomize transaction.")
            end
            if (req.SRC_RDY == 1'b1) begin
                for (int unsigned it = 0; it < ITEMS; it++) begin
                    if (req.VLD[it] == 1'b1) begin
                        byte_array::sequence_item tmp_packet;
                        header_export.get(tmp_packet);
                        req.DATA[it][16-1:0] = tmp_packet.size();
                    end
                end
            end
            finish_item(req);

            // Get response from driver
            get_response(rsp);

            reset = p_sequencer.reset_sync.has_been_reset();
            while (rsp.SRC_RDY != 0 && !rsp.DST_RDY && !reset) begin
                start_item(req);
                finish_item(req);
                get_response(rsp);
            end
        end
    endtask
endclass

class mvb_sequence_lib#(ITEMS, ITEM_WIDTH) extends uvm_sequence_library#(mvb::sequence_item#(ITEMS, ITEM_WIDTH));
  `uvm_object_param_utils(top_agent::mvb_sequence_lib#(ITEMS, ITEM_WIDTH))
  `uvm_sequence_library_utils(top_agent::mvb_sequence_lib#(ITEMS, ITEM_WIDTH))

    function new(string name = "");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence();
        this.add_sequence(mvb_sequence_simple #(ITEMS, ITEM_WIDTH)::get_type());
    endfunction
endclass

