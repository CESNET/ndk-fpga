/*
 * file       : sequence.sv
 * description: PMA sequence
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * Copyright (C) 2021 CESNET z. s. p. o.
*/

// This low level sequence define how can data looks like.
class sequence_hdr_err_inj #(int unsigned DATA_WIDTH) extends uvm_sequence #(uvm_pma::sequence_item #(DATA_WIDTH));

    `uvm_object_param_utils(uvm_byte_array_pma::sequence_hdr_err_inj #(DATA_WIDTH))
    `uvm_declare_p_sequencer(uvm_pma::sequencer #(DATA_WIDTH))

    // -----------------------
    // Parameters.
    // -----------------------

    localparam BYTE_NUM = DATA_WIDTH/8;

    logic [DATA_WIDTH-1 : 0]     data = 0;
    logic [(DATA_WIDTH-8)-1 : 0] start_data = 0;
    int                          frame_cnt = 0;

    uvm_byte_array_pma::data_reg simple_reg;
    // High level transaction
    uvm_byte_array::sequence_item frame;
    // High level sequencer
    uvm_byte_array_pma::sequencer hi_sqr;

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
    endfunction: new

    task try_get();
        if (frame == null && hl_transactions != 0) begin
            hi_sqr.m_packet.try_next_item(frame);
            if (frame != null) begin
                hl_transactions--;
            end
        end
    endtask


    // Generates transactions
    task body;

        if(!uvm_config_db #(uvm_byte_array_pma::sequencer)::get(p_sequencer, "", "hi_sqr", hi_sqr)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        if(!uvm_config_db #(uvm_byte_array_pma::data_reg)::get(p_sequencer, "", "simple_reg", simple_reg)) begin
            simple_reg = new();
            uvm_config_db #(uvm_byte_array_pma::data_reg)::set(p_sequencer, "", "simple_reg", simple_reg);
        end


        `uvm_info(get_full_name(), "sequence_hdr_err_inj is running", UVM_LOW)
        // Create a request for sequence item
        req = uvm_pma::sequence_item #(DATA_WIDTH)::type_id::create("req");
        while (hl_transactions > 0 || frame != null) begin
            try_get();
            // Send frame
            if (frame != null) begin
                if (frame.data.size() != 0) begin
                    send_data(frame);
                end
                frame = null;
                hi_sqr.m_packet.item_done();
            end else begin
                send_empty();
            end
        end
    endtask

    task send_data(uvm_byte_array::sequence_item frame);
            for (int i = ((BYTE_NUM-1)+BYTE_NUM); i < frame.data.size(); i = i + BYTE_NUM) begin
                // Together with finish_item initiate operation of sequence item (handshake with driver).
                start_item(req);
                req.block_lock = 1'b1;
                send_same();

                if(i % 8 == 7) begin
                    void'(std::randomize(req.hdr) with {req.hdr inside {0, 3, 4};});
                    req.hdr_vld = 1'b1;
                end else begin
                    req.hdr_vld = 1'b0;
                end

                // Data are divided to 8 bytes long chunks, which are sended to driver.
                req.data = {<< byte{frame.data[i +: BYTE_NUM]}};

                scramble(req);
                finish_item(req);
            end
    endtask

    task scramble(uvm_pma::sequence_item #(DATA_WIDTH) req);
        logic [DATA_WIDTH-1 : 0] scrambled_data;

        for (int i=0; i<DATA_WIDTH; i++) begin
            scrambled_data[i] = req.data[i] ^ simple_reg.scramble_reg[38] ^ simple_reg.scramble_reg[57];
            simple_reg.scramble_reg      <<= 1;
            simple_reg.scramble_reg[0]   = scrambled_data[i];
        end
        req.data = scrambled_data;
        data_vld_trigger();
    endtask

    task send_empty();
        start_item(req);
        finish_item(req);
    endtask

    task data_vld_trigger();
        simple_reg.it++;
        if (simple_reg.it == 32) begin
            req.data_vld = 1'b0;
            simple_reg.it = 0;
        end else begin
            req.data_vld = 1'b1;
        end
        simple_reg.data_vld = req.data_vld;
        simple_reg.hdr_vld = req.hdr_vld;
        simple_reg.data = req.data;
        simple_reg.hdr = req.hdr;
    endtask

    task send_same();
        while (!simple_reg.data_vld) begin
            req.data_vld = 1'b1;
            simple_reg.data_vld = req.data_vld;

            req.hdr_vld = simple_reg.hdr_vld;
            req.data = simple_reg.data;
            req.hdr = simple_reg.hdr;
            finish_item(req);
            start_item(req);
        end
    endtask

endclass
