/*
 * file       : sequence_simple_tx_mac.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: LII sequence
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequence_simple #(int unsigned DATA_WIDTH, logic FAST_SOF, int unsigned META_WIDTH, int unsigned LOGIC_WIDTH, int unsigned SOF_WIDTH) extends uvm_sequence #(uvm_lii::sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH));

    `uvm_object_param_utils(uvm_byte_array_lii::sequence_simple #(DATA_WIDTH, FAST_SOF, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH))
    `uvm_declare_p_sequencer(uvm_lii::sequencer #(DATA_WIDTH, META_WIDTH, SOF_WIDTH))

    // -----------------------
    // Parameters.
    // -----------------------

    localparam BYTE_NUM = DATA_WIDTH/8;

    // High level transaction
    uvm_byte_array::sequence_item frame;
    // High level sequencer
    uvm_byte_array_lii::sequencer #(LOGIC_WIDTH) hi_sqr;
    //common::rand_length number_of_idles;

    uvm_logic_vector::sequence_item #(LOGIC_WIDTH) meta;

    localparam BYTES_VLD_LENGTH        = $clog2(DATA_WIDTH/8)+1;
    logic [31 : 0] idle                = 32'h55555555;
    logic [31 : 0] preambule           = 32'hd5555555;
    logic [BYTES_VLD_LENGTH : 0] bytes = '0;
    bit preambule_done                 = 1'b0;
    logic error_trig                   = 1'b0;
    logic link_down                    = 1'b0;
    bit idle_done                      = 1'b0;
    int frame_cnt                      = 0;
    string name;

    //////////////////////////////////
    // RANDOMIZATION
    rand int unsigned hl_transactions;
    int unsigned hl_transactions_min = 10;
    int unsigned hl_transactions_max = 200;

    constraint c_hl_transactions{
        hl_transactions inside {[hl_transactions_min:hl_transactions_max]};
    };

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
        this.name = name;
        //number_of_idles    = common::rand_length_rand::new();
    endfunction

    virtual task create_sequence_item();
    endtask

    task set_default();
        req.sof         = '0;
        req.eof         = 1'b0;
        req.eeof        = 1'b0;
        req.link_status = 1'b1;
        req.rxdecerr    = 1'b0;
        req.rxseqerr    = 1'b0;
        req.crcerr      = 1'b0;
        req.edb         = '0;
        req.bytes_vld   = '0;
        req.meta        = '0;
    endtask

    task set_meta();
        meta.data[0]    = !req.link_status;
        meta.data[1]    = error_trig;
        meta.data[2]    = req.rxseqerr;
    endtask

    task try_get();
        if (frame == null && hl_transactions != 0) begin
            hi_sqr.m_packet.try_next_item(frame);
            if (frame != null) begin
                hl_transactions--;
                hi_sqr.m_meta.get_next_item(meta);
            end
        end
    endtask

    // Generates transactions
    task body;
        // Create a request for sequence item
        if(!uvm_config_db #(uvm_byte_array_lii::sequencer #(LOGIC_WIDTH))::get(p_sequencer, "", "hi_sqr", hi_sqr)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end
        `uvm_info(get_full_name(), $sformatf("%s is running", name), UVM_DEBUG)
        req = uvm_lii::sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)::type_id::create("req");
        while (hl_transactions > 0 || frame != null) begin
            try_get();
            // Send frame
            error_trig     = 1'b0;
            preambule_done = 1'b0;
            idle_done      = 1'b0;

            if (frame != null) begin
                if (frame.data.size() != 0) begin
                    send(frame);
                end
                frame = null;
                hi_sqr.m_packet.item_done();
                hi_sqr.m_meta.item_done();
            end else begin
                send_empty();
            end
        end
    endtask
    // Method which define how the transaction will look.
    task send(uvm_byte_array::sequence_item frame);
        send_empty();
        create_sequence_item();
    endtask

    virtual task send_empty();
        start_item(req);
        //void'(std::randomize(req.data));
        req.data        = '0;
        req.bytes_vld   = '0;
        req.sof         = '0;
        req.eof         = 1'b0;
        req.eeof        = 1'b0;
        req.edb         = '0;
        req.link_status = 1'b1;
        req.meta        = '0;
        req.rxdecerr    = 1'b0;
        req.rxseqerr    = 1'b0;
        req.crcerr      = 1'b0;
        finish_item(req);
        send_same();
    endtask

    task send_same();
        // Get response from driver
        get_response(rsp);
        while (!rsp.rdy) begin
            start_item(req);
            finish_item(req);
            get_response(rsp);
        end
    endtask

endclass
