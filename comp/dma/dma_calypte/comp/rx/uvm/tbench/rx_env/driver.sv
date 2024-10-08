//-- driver.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class driver#(CHANNELS, PKT_SIZE_MAX) extends uvm_component;
    `uvm_component_param_utils(uvm_dma_ll_rx::driver#(CHANNELS, PKT_SIZE_MAX))

    localparam MFB_META_WIDTH = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);

    uvm_seq_item_pull_port #(uvm_byte_array::sequence_item, uvm_byte_array::sequence_item)   seq_item_port_byte_array;

    mailbox#(uvm_byte_array::sequence_item)   byte_array_export;
    mailbox#(uvm_logic_vector::sequence_item#(MFB_META_WIDTH)) logic_vector_export;
    local semaphore sem;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);

        seq_item_port_byte_array = new("seq_item_port_byte_array", this);

        byte_array_export   = new(1);
        logic_vector_export = new(1);
        sem = new(1);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (byte_array_export.num() != 0);
        ret |= (logic_vector_export.num() != 0);
        return ret;
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        uvm_byte_array::sequence_item                    byte_array_req;
        uvm_byte_array::sequence_item                    byte_array_new;
        uvm_logic_vector::sequence_item#(MFB_META_WIDTH) logic_vector_new;

        logic [$clog2(PKT_SIZE_MAX+1)-1:0] packet_size;
        int unsigned channel;
        logic [24-1:0] meta;
        string         msg = "\n";

        forever begin
            // Get new sequence item to drive to interface
            seq_item_port_byte_array.get_next_item(byte_array_req);

            msg = {msg, $sformatf("-------------------------------------------------------\n")};
            msg = {msg, $sformatf("DRIVER: Got new transaction:\n")};
            msg = {msg, $sformatf("-------------------------------------------------------\n")};
            msg = {msg, $sformatf("%s\n", byte_array_req.convert2string())};


            assert(std::randomize(channel) with {channel >= 0; channel < CHANNELS;});
            assert(std::randomize(meta));

            msg = {msg, $sformatf("\nChannel: %0d\n", channel)};
            msg = {msg, $sformatf("Meta: 0x%x\n", meta)};

            $cast(byte_array_new, byte_array_req.clone());
            logic_vector_new  = uvm_logic_vector::sequence_item#(MFB_META_WIDTH)::type_id::create("logic_vector_new");
            packet_size  = byte_array_new.data.size();
            logic_vector_new.data = {packet_size, channel, meta};
            msg = {msg, $sformatf("Pkt size: %0d\n", packet_size)};

            `uvm_info(this.get_full_name(), msg, UVM_HIGH);

            wait(byte_array_export.num() == 0 || logic_vector_export.num() == 0);
            sem.get(1);
            byte_array_export.put(byte_array_new);
            logic_vector_export.put(logic_vector_new);
            sem.put(1);

            seq_item_port_byte_array.item_done();
        end
    endtask

endclass

