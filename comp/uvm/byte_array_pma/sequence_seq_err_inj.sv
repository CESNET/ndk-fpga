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
class sequence_seq_err_inj #(int unsigned DATA_WIDTH) extends uvm_sequence #(uvm_pma::sequence_item #(DATA_WIDTH));

    `uvm_object_param_utils(uvm_byte_array_pma::sequence_seq_err_inj #(DATA_WIDTH))
    `uvm_declare_p_sequencer(uvm_pma::sequencer #(DATA_WIDTH))

    // -----------------------
    // Parameters.
    // -----------------------

    localparam BYTE_NUM = DATA_WIDTH/8;
    localparam IDLE_C = 7'b0000000; // IDLE code, 0x00

    logic [DATA_WIDTH-1 : 0]     data = 0;
    logic [(DATA_WIDTH-8)-1 : 0] start_data = 0;
    //logic [57 : 0]               scramble_reg = 58'h0;
    logic [8-1 : 0]              state = uvm_pma::BT_C_C;
    logic [8-1 : 0]              terminate;
    logic [8-1 : 0]              start_seq;
    bit                          done = 0;
    bit                          high_level_tr_done = 0;
    int                          bytes_vld = 0;
    rand int unsigned            number_of_idles;

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
        `uvm_info(get_full_name(), "sequence_seq_err_inj is running", UVM_LOW)
        // Create a request for sequence item
        req = uvm_pma::sequence_item #(DATA_WIDTH)::type_id::create("req");
        while (hl_transactions > 0 || frame != null) begin
            try_get();
            void'(std::randomize(number_of_idles) with{number_of_idles inside {[20 : 50]}; (number_of_idles % 2 == 0);});

            if (frame != null) begin
                if (frame.data.size() != 0) begin
                    while (high_level_tr_done == 1'b0) begin
                        case (state)
                            uvm_pma::BT_C_C :
                                for (int i=0; i < number_of_idles; i++) begin
                                    send_idle();
                                    if(i == (number_of_idles - 1)) begin
                                        state = uvm_pma::BT_S_D;
                                        done  = 0;
                                    end
                                end
                            uvm_pma::BT_S_D : send_start(frame);
                            8'b10000000 : send_data(frame);
                            uvm_pma::BT_T_C : send_terminate(frame);
                        endcase
                    end
                    void'(std::randomize(number_of_idles) with{number_of_idles inside {[20 : 50]}; (number_of_idles % 2 == 0);});
                    for (int i=0; i < number_of_idles; i++) begin
                        send_idle();
                        if(i == (number_of_idles - 1)) begin
                            state = uvm_pma::BT_C_C;
                            done  = 0;
                        end
                    end
                end
                frame = null;
            end else begin
                send_empty();
            end
            if(high_level_tr_done == 1'b1) begin
                hi_sqr.m_packet.item_done();
                high_level_tr_done = 1'b0;
            end
        end
    endtask

    // Generate start sequence. In first transaction send one state byte and three idles, in second send four byte of idles only.
    task send_idle();
        start_item(req);
        req.block_lock = 1'b1;
        send_same();

        if (done == 1'b0) begin
            req.hdr     = uvm_pma::C_HDR;
            req.hdr_vld = 1'b1;
            req.data    = {IDLE_C, IDLE_C, IDLE_C, 3'b000, uvm_pma::BT_C_C};
            done        = 1'b1;
        end else begin
            req.hdr_vld = 1'b0;
            req.data    = {IDLE_C, IDLE_C, IDLE_C, IDLE_C, 4'b0000};
            state       = uvm_pma::BT_S_D;
            done        = 1'b0;
        end
        scramble(req);
        finish_item(req);

        // Send error data once per 8 transactions.
        if((((simple_reg.it % 8) == 0) && simple_reg.it != 0) && req.hdr_vld == 1'b0) begin
           send_error_data();
        end
        if ((((simple_reg.it % 16) == 0) && simple_reg.it != 0) && req.hdr_vld == 1'b0) begin
            send_error_terminate();
        end
        if((((simple_reg.it % 18) == 0) && simple_reg.it != 0) && req.hdr_vld == 1'b0) begin
            send_error_seq();
            return;
        end
    endtask

// Tests for error SEQERR injection
    task send_error_idle();
        start_item(req);
        send_same();

        req.hdr     = uvm_pma::C_HDR;
        req.hdr_vld = 1'b1;
        req.data    = {IDLE_C, IDLE_C, IDLE_C, 3'b000, uvm_pma::BT_C_C};

        scramble(req);
        finish_item(req);

        start_item(req);

        send_same();

        req.hdr_vld = 1'b0;
        req.data    = {IDLE_C, IDLE_C, IDLE_C, IDLE_C, 4'b0000};

        scramble(req);
        finish_item(req);
    endtask

    task send_error_data();
        state     = uvm_pma::BT_C_C;

        start_item(req);
        send_same();

        req.hdr     = uvm_pma::D_HDR;
        req.hdr_vld = 1'b1;
        void'(std::randomize(req.data));

        scramble(req);
        finish_item(req);

        start_item(req);
        send_same();

        req.hdr_vld = 1'b0;
        void'(std::randomize(req.data));

        scramble(req);
        finish_item(req);

    endtask


    task send_error_terminate();
        state     = uvm_pma::BT_C_C;
        void'(std::randomize(terminate) with {terminate inside {uvm_pma::BT_T_C,  uvm_pma::BT_D1_C,
                                                          uvm_pma::BT_D2_C, uvm_pma::BT_D3_C,
                                                          uvm_pma::BT_D4_C, uvm_pma::BT_D5_C,
                                                          uvm_pma::BT_D6_C, uvm_pma::BT_D7_T};});

        start_item(req);
        send_same();

        req.hdr     = uvm_pma::C_HDR;
        req.hdr_vld = 1'b1;

        // Data are divided to 8 bytes long chunks, which are sended to driver.
        void'(std::randomize(start_data));
        req.data = {start_data, terminate};

        req.data[31 : 8] = start_data;
        req.data[7 : 0]  = terminate;

        scramble(req);
        finish_item(req);

        start_item(req);
        send_same();

        req.hdr_vld = 1'b0;
        void'(std::randomize(req.data));

        scramble(req);
        finish_item(req);

    endtask

    task send_error_start();

        void'(std::randomize(start_seq) with {start_seq inside {uvm_pma::BT_C_S, uvm_pma::BT_S_D, uvm_pma::BT_O_S};});

        start_item(req);
        send_same();

        req.hdr     = uvm_pma::C_HDR;
        req.hdr_vld = 1'b1;

        // Data are divided to 8 bytes long chunks, which are sended to driver.
        void'(std::randomize(start_data));
        req.data = {start_data, start_seq};

        scramble(req);
        finish_item(req);

        start_item(req);
        send_same();

        req.hdr_vld = 1'b0;
        void'(std::randomize(req.data));

        scramble(req);
        finish_item(req);
    endtask

    task send_error_seq();

        start_seq = uvm_pma::UNKNOWN;

        start_item(req);
        send_same();

        req.hdr     = uvm_pma::C_HDR;
        req.hdr_vld = 1'b1;

        // Data are divided to 8 bytes long chunks, which are sended to driver.
        void'(std::randomize(start_data));
        req.data = {start_data, start_seq};

        scramble(req);
        finish_item(req);

        start_item(req);
        send_same();

        req.hdr_vld = 1'b0;
        void'(std::randomize(req.data));

        scramble(req);
        finish_item(req);
    endtask


    // Method for generation of start sequence.
    task send_start(uvm_byte_array::sequence_item frame);
        void'(std::randomize(start_seq) with {start_seq inside {uvm_pma::BT_C_S, uvm_pma::BT_S_D, uvm_pma::BT_O_S};});

        start_item(req);
        send_same();

        if (done == 1'b0) begin
            req.hdr     = uvm_pma::C_HDR;
            req.hdr_vld = 1'b1;
            if (start_seq == uvm_pma::BT_S_D) begin
                start_data  = {<< byte{frame.data[0 +: 3]}};
                req.data    = {start_data, start_seq};
            end
            else if (start_seq == uvm_pma::BT_C_S) begin
                req.data    = {24'b000000000000000000000000, start_seq};
            end
            else if (start_seq == uvm_pma::BT_O_S) begin
                void'(std::randomize(start_data));
                req.data    = {start_data, start_seq};
            end
            done        = 1'b1;
        end else begin
            req.hdr_vld = 1'b0;
            req.data    = {<< byte{frame.data[3 +: BYTE_NUM]}};
            state       = 8'b10000000;
            bytes_vld   = ((frame.data.size() - ((BYTE_NUM-1)+BYTE_NUM)) % 8);
            done        = 1'b0;
        end

        scramble(req);
        finish_item(req);
    endtask

    task insert_data(int length);
            for (int i = ((BYTE_NUM-1)+BYTE_NUM); i < length; i = i + BYTE_NUM) begin
                // Together with finish_item initiate operation of sequence item (handshake with driver).
                start_item(req);
                send_same();

                if(i % 8 == 7) begin
                    req.hdr     = uvm_pma::D_HDR;
                    req.hdr_vld = 1'b1;
                end else begin
                    req.hdr_vld = 1'b0;
                end

                // Data are divided to 8 bytes long chunks, which are sended to driver.
                req.data = {<< byte{frame.data[i +: BYTE_NUM]}};

                scramble(req);
                finish_item(req);

                if((((simple_reg.it % 12) == 0) && simple_reg.it != 0) && req.hdr_vld == 1'b0) begin
                    send_error_idle();
                    state = uvm_pma::BT_C_C;
                    high_level_tr_done = 1'b1;
                    return;
                end
                if((((simple_reg.it % 20) == 0) && simple_reg.it != 0) && req.hdr_vld == 1'b0) begin
                    send_error_start();
                    state = uvm_pma::BT_C_C;
                    high_level_tr_done = 1'b1;
                    return;
                end

                if((((simple_reg.it % 16) == 0) && simple_reg.it != 0) && req.hdr_vld == 1'b0) begin
                    send_error_seq();
                    state = uvm_pma::BT_C_C;
                    high_level_tr_done = 1'b1;
                    return;
                end
            end
    endtask

    // Method which define how the transaction will look.
    task send_data(uvm_byte_array::sequence_item frame);

        if ((bytes_vld % 8) == 0) begin
            insert_data(frame.data.size());
            bytes_vld = 0;
            state     = uvm_pma::BT_T_C;
        end else begin
            state = uvm_pma::BT_T_C;
            insert_data(frame.data.size() - bytes_vld);
        end
    endtask

    task send_terminate(uvm_byte_array::sequence_item frame);
        int i = frame.data.size() - bytes_vld;
        int j = frame.data.size() - bytes_vld + (BYTE_NUM-1);
        start_item(req);
        send_same();

        if (bytes_vld == 0) begin
            if (done == 1'b0) begin
                req.hdr           = uvm_pma::C_HDR;
                req.hdr_vld       = 1'b1;
                req.data[7 : 0] = uvm_pma::BT_T_C;
                req.data[31 : 8]  = 24'b000000000000000000000000;
                done              = 1'b1;
            end else begin
                req.data           = {IDLE_C, IDLE_C, IDLE_C, IDLE_C, 4'b0000};
                req.hdr_vld        = 1'b0;
                high_level_tr_done = 1'b1;
                done               = 1'b0;
                state              = uvm_pma::BT_C_C;
            end
        end

        if (bytes_vld == 1) begin
            if (done == 1'b0) begin
                req.hdr           = uvm_pma::C_HDR;
                req.hdr_vld       = 1'b1;
                data              = {<< byte{frame.data[i +: 1]}};
                req.data[15 : 8] = data[31 : 24];
                req.data[31 : 16]  = 16'b0000000000000000;
                req.data[7 : 0] = uvm_pma::BT_D1_C;
                done              = 1'b1;
            end else begin
                req.data           = {IDLE_C, IDLE_C, IDLE_C, IDLE_C, 4'b0000};
                req.hdr_vld        = 1'b0;
                high_level_tr_done = 1'b1;
                done               = 1'b0;
                state              = uvm_pma::BT_C_C;
            end
        end
        if (bytes_vld == 2) begin
            if (done == 1'b0) begin
                req.hdr           = uvm_pma::C_HDR;
                req.hdr_vld       = 1'b1;
                data              = {<< byte{frame.data[i +: 2]}};
                req.data[23 : 8] = data[31 : 16];
                req.data[7 : 0]  = uvm_pma::BT_D2_C;
                req.data[31 : 24]   = 8'b00000000;
                done              = 1'b1;
            end else begin
                req.data           = {IDLE_C, IDLE_C, IDLE_C, IDLE_C, 4'b0000};
                req.hdr_vld        = 1'b0;
                high_level_tr_done = 1'b1;
                done               = 1'b0;
                state              = uvm_pma::BT_C_C;
            end
        end
        if (bytes_vld == 3) begin
            if (done == 1'b0) begin
                req.hdr          = uvm_pma::C_HDR;
                req.hdr_vld      = 1'b1;
                data             = {<< byte{frame.data[i +: 3]}};
                req.data[31 : 8] = data[31 : 8];
                req.data[7 : 0]  = uvm_pma::BT_D3_C;
                done             = 1'b1;
            end else begin
                req.data           = {IDLE_C, IDLE_C, IDLE_C, IDLE_C, 4'b0000};
                req.hdr_vld        = 1'b0;
                high_level_tr_done = 1'b1;
                done               = 1'b0;
                state              = uvm_pma::BT_C_C;
            end
        end
        if (bytes_vld == 4) begin
            if (done == 1'b0) begin
                req.hdr     = uvm_pma::C_HDR;
                req.hdr_vld = 1'b1;
                data             = {<< byte{frame.data[i +: 3]}};
                req.data[31 : 8] = data[31 : 8];
                req.data[7 : 0]  = uvm_pma::BT_D4_C;
                done        = 1'b1;
            end else begin
                req.hdr_vld        = 1'b0;
                data               = {<< byte{frame.data[j +: 1]}};
                req.data[7 : 0]  = data[31 : 24];
                req.data[31 : 8]   = 24'b0000000000000000;
                high_level_tr_done = 1'b1;
                done               = 1'b0;
                state              = uvm_pma::BT_C_C;
            end
        end
        if (bytes_vld == 5) begin
            if (done == 1'b0) begin
                req.hdr     = uvm_pma::C_HDR;
                req.hdr_vld = 1'b1;
                data             = {<< byte{frame.data[i +: 3]}};
                req.data[31 : 8] = data[31 : 8];
                req.data[7 : 0]  = uvm_pma::BT_D5_C;
                done        = 1'b1;
            end else begin
                req.hdr_vld        = 1'b0;
                data               = {<< byte{frame.data[j +: 2]}};
                req.data[15 : 0]  = data[31 : 16];
                req.data[31 : 16]   = 16'b0000000000000000;
                high_level_tr_done = 1'b1;
                done               = 1'b0;
                state              = uvm_pma::BT_C_C;
            end
        end
        if (bytes_vld == 6) begin
            if (done == 1'b0) begin
                req.hdr     = uvm_pma::C_HDR;
                req.hdr_vld = 1'b1;
                data             = {<< byte{frame.data[i +: 3]}};
                req.data[31 : 8] = data[31 : 8];
                req.data[7 : 0]  = uvm_pma::BT_D6_C;
                done        = 1'b1;
            end else begin
                data = 0;
                req.hdr_vld        = 1'b0;
                data               = {<< byte{frame.data[j +: 3]}};
                req.data[23 : 0]  = data[31 : 8];
                req.data[31 : 24]    = 8'b00000000;
                high_level_tr_done = 1'b1;
                done               = 1'b0;
                state              = uvm_pma::BT_C_C;
            end
        end
        if (bytes_vld == 7) begin
            if (done == 1'b0) begin
                req.hdr     = uvm_pma::C_HDR;
                req.hdr_vld = 1'b1;
                data             = {<< byte{frame.data[i +: 3]}};
                req.data[31 : 8] = data[31 : 8];
                req.data[7 : 0]  = uvm_pma::BT_D7_T;
                done        = 1'b1;
            end else begin
                req.hdr_vld        = 1'b0;
                data               = {<< byte{frame.data[j +: 4]}};
                req.data[31 : 0]   = data[31 : 0];
                high_level_tr_done = 1'b1;
                done               = 1'b0;
                state              = uvm_pma::BT_C_C;
            end
        end
        scramble(req);
        finish_item(req);
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
