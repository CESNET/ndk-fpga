/*
 * file       : sequence_simple_tx_mac.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: LII sequence
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

// PCS and TX_MAC

// This low level sequence define how can data looks like.
// This sequence generate random gaps between frames and simulate basic functionality of TX MAC
// So it can be used in TX MAC as an input sequence
// In this sequence is link status set to logic 1 all the time, beacause TX MAC does not has any link status
// There is also logic vector sequence item for generation of error signals
class sequence_simple_tx_mac #(int unsigned DATA_WIDTH, logic FAST_SOF, int unsigned META_WIDTH, int unsigned LOGIC_WIDTH, int unsigned SOF_WIDTH) extends sequence_simple #(DATA_WIDTH, FAST_SOF, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH);

    `uvm_object_param_utils(uvm_byte_array_lii::sequence_simple_tx_mac #(DATA_WIDTH, FAST_SOF, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH))

    // -----------------------
    // Parameters.
    // -----------------------

    localparam BYTE_NUM = DATA_WIDTH/8;

    uvm_common::rand_length number_of_idles;

    localparam BYTES_VLD_LENGTH        = $clog2(DATA_WIDTH/8)+1;
    logic [BYTES_VLD_LENGTH : 0] bytes = '0;

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new("sequence_simple_tx_mac");
        number_of_idles    = uvm_common::rand_length_stable::new();
    endfunction

    // Method which define how the transaction will look.
    virtual task create_sequence_item();
        for (int i = 0; i < frame.data.size(); i = i + BYTE_NUM) begin
            // Together with finish_item initiate operation of sequence item (handshake with driver).

            start_item(req);
            if (!req.randomize()) `uvm_fatal(this.get_full_name(), "failed to radnomize");

            set_default();

            // First chunk has SOF = 1
            if (i == 0) begin
                while (number_of_idles.m_value != 0) begin
                    number_of_idles.m_value--;
                    finish_item(req);
                    send_same();
                    start_item(req);
                end

                // SFD and Preambule logic
                while (preambule_done != 1'b1) begin
                    // SFD generation
                    if (idle_done == 1'b0) begin
                        // First chunk has SOF = 1
                        req.sof   = 1'b1;
                        req.data  = idle;
                        idle_done = 1'b1;
                        finish_item(req);
                    // Preambule generation
                    end else begin
                        req.sof        = 1'b0;
                        req.data       = preambule;
                        preambule_done = 1'b1;
                        finish_item(req);
                    end
                    send_same();
                    start_item(req);
                    set_default();
                end
            end

            // Data are divided to 32 bytes long chunks, which are sended to driver.
            req.data = {<< byte{frame.data[i +: BYTE_NUM]}};

            if ((frame.data.size() % BYTE_NUM) == 0) begin
                bytes = BYTE_NUM;
            end else begin
                bytes = (frame.data.size() % BYTE_NUM);
            end

            if ((i + (BYTE_NUM + bytes) == frame.data.size()) && FAST_SOF == 1'b1) begin
                req.eeof = 1'b1;
                req.edb = bytes;
            end

            // Last chunk has EOF = 1
            //FOR TX MAC
            if (i + BYTE_NUM >= frame.data.size()) begin
                req.eof = 1'b1;
                req.bytes_vld = bytes;
            end

            finish_item(req);
            send_same();
        end
    endtask

endclass
