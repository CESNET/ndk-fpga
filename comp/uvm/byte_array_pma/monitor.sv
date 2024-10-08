/*
 * file       : monitor.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: uvm_byte_array to uvm_pma monitor
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef TEST_MONITOR_SV
`define TEST_MONITOR_SV

class monitor #(int unsigned DATA_WIDTH) extends uvm_byte_array::monitor;

    `uvm_component_param_utils(uvm_byte_array_pma::monitor #(DATA_WIDTH))

    // Analysis port
    uvm_analysis_imp #(uvm_pma::sequence_item #(DATA_WIDTH), monitor #(DATA_WIDTH)) analysis_export;
    uvm_byte_array::sequence_item h_tr;
    local byte unsigned tr_data_fifo[$];
    // Variables
    logic [57 : 0]  descramble_reg;
    local int       BYTE_NUM = DATA_WIDTH/8;
    localparam FIRST_WORD    = 0;
    localparam IDLE          = 1;
    localparam INFRAME       = 2;
    localparam LAST_WORD     = 3;
    localparam LINK_DOWN     = 4;
    localparam TIMER_125US   = 19531;
    int timer_cnt            = 0;
    int state                = FIRST_WORD;
    int hdr_err              = 0;
    int hdr_err_prev         = 0;
    bit timer_cnt_en         = 1'b0;
    logic hi_ber             = 1'b0;

    function new (string name, uvm_component parent);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
        descramble_reg  = 58'h0;
    endfunction

    function void descramble(uvm_pma::sequence_item #(DATA_WIDTH) tr);
        logic [DATA_WIDTH-1 : 0] dout;

        for (int i=0; i<DATA_WIDTH; i++) begin
            dout[i]           = tr.data[i] ^ descramble_reg[38] ^ descramble_reg[57];
            descramble_reg    <<= 1;
            descramble_reg[0] = tr.data[i];
        end
        tr.data = dout;
    endfunction

    function int check_header(bit hdr_vld, logic [1 : 0] hdr);
        if(hdr_vld == 1'b1) begin
            if (hdr == uvm_pma::C_HDR) begin
                return 1;
            end
            else if (hdr == uvm_pma::D_HDR) begin
                return 2;
            end else begin
                hdr_err_prev = hdr_err;
                hdr_err++;
                return 0;
            end
        end
    endfunction

    function void insert_header(bit hdr_vld, logic [1 : 0] hdr);
        if(hdr_vld == 1'b1) begin
            tr_data_fifo.push_back(hdr);
        end
    endfunction

    function void check_sequence(logic [31 : 0] data, int hdr_type);
        if (hdr_type == 1) begin
            if (data[7 : 0] == uvm_pma::BT_S_D || data[7 : 0] == uvm_pma::BT_C_S || data[7 : 0] == uvm_pma::BT_O_S) begin
                state = INFRAME;
            end
            else if (data[7 : 0] == uvm_pma::BT_T_C  || data[7 : 0] == uvm_pma::BT_D1_C  ||
                     data[7 : 0] == uvm_pma::BT_D2_C || data[7 : 0] == uvm_pma::BT_D3_C  ||
                     data[7 : 0] == uvm_pma::BT_D4_C || data[7 : 0] == uvm_pma::BT_D5_C ||
                     data[7 : 0] == uvm_pma::BT_D6_C || data[7 : 0] == uvm_pma::BT_D7_T)
            begin
                state = LAST_WORD;
            end
            else if (data == 32'h0000001e && state == INFRAME) begin
                state = LAST_WORD;
            end
        end
    endfunction

    function void insert_data(logic [31 : 0] data);
        for (int i = 0; i < BYTE_NUM; i++) begin
            tr_data_fifo.push_back(data[((i+1)*8)-1 -: 8]);
        end
    endfunction

    // Write 32 transactions to data stream and send it to scoreboard.
    virtual function void write(uvm_pma::sequence_item #(DATA_WIDTH) tr);
        if (tr.hdr_vld == 1'b1 && timer_cnt_en == 1'b1) begin
            if (timer_cnt >= TIMER_125US && state != LINK_DOWN) begin
                timer_cnt = 0;
            end
            timer_cnt++;
        end
        if (tr.data_vld == 1'b1) begin
            if (hdr_err >= 16) begin
                tr_data_fifo.delete();
                state = LINK_DOWN;
                hi_ber = 1'b1;
            end else begin
                hi_ber = 1'b0;
            end
            descramble(tr);
            case (state)
                FIRST_WORD :
                    begin
                        tr_data_fifo.delete();
                        check_header(tr.hdr_vld, tr.hdr);
                        if (tr.data == 32'h0000001e) begin
                            timer_cnt_en = 1'b1;
                            state = IDLE;
                            insert_header(tr.hdr_vld, tr.hdr);
                            insert_data(tr.data);
                        end
                    end
                IDLE :
                    begin
                        check_sequence(tr.data, check_header(tr.hdr_vld, tr.hdr));
                        insert_header(tr.hdr_vld, tr.hdr);
                        insert_data(tr.data);
                    end
                INFRAME :
                    begin
                        check_sequence(tr.data, check_header(tr.hdr_vld, tr.hdr));
                        insert_header(tr.hdr_vld, tr.hdr);
                        insert_data(tr.data);
                    end
                LAST_WORD :
                    begin
                        check_sequence(tr.data, check_header(tr.hdr_vld, tr.hdr));
                        insert_header(tr.hdr_vld, tr.hdr);
                        insert_data(tr.data);
                        h_tr    = uvm_byte_array::sequence_item::type_id::create("h_tr");
                        h_tr.data = new[tr_data_fifo.size()];
                        h_tr.data = tr_data_fifo;
                        analysis_port.write(h_tr);
                        tr_data_fifo.delete();
                        state = FIRST_WORD;
                    end
                LINK_DOWN :
                    begin
                        if (timer_cnt >= TIMER_125US) begin
                            timer_cnt = 0;
                            if (tr.data == 32'h0000001e) begin
                                state = IDLE;
                                insert_header(tr.hdr_vld, tr.hdr);
                                insert_data(tr.data);
                            end else begin
                                state = FIRST_WORD;
                            end
                            if (hi_ber == 1'b1) begin
                                state = LINK_DOWN;
                                $write("\nLINK DOWN!!!! %t HDR ERR %d HDR previous %d \n", $time, hdr_err, hdr_err_prev);
                                hdr_err_prev = hdr_err;
                            end
                            hdr_err = 0;
                        end
                        check_header(tr.hdr_vld, tr.hdr);
                    end
            endcase
        end
    endfunction

endclass

`endif
