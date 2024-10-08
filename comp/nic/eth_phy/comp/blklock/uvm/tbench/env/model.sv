/*
 * file       : model.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM Model for Block lock
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

 class model #(SH_CNT_MAX, SH_INVALID_CNT_MAX, SLIP_WAIT_TIME) extends uvm_component;
    `uvm_component_param_utils(uvm_blklock::model #(SH_CNT_MAX, SH_INVALID_CNT_MAX, SLIP_WAIT_TIME))

    uvm_tlm_analysis_fifo #(uvm_mvb::sequence_item#(1, 2)) input_data;
    uvm_tlm_analysis_fifo #(uvm_reset::sequence_item) reset;

    uvm_analysis_port #(uvm_logic_vector::sequence_item#(2)) output_data;

    local int unsigned sh_cnt = 0;
    local int unsigned sh_invalid_cnt = 0;
    local bit rx_lock_aquired = 2'b0;
    local bit rx_lock_aquired_reg1 = 2'b0;
    local bit slip_cmd_out = 2'b0;
    local bit slip_cmd = 2'b0;
    local bit slip_cmd_reg = 2'b0;
    local bit prev_slip_cmd = 2'b0;
    local int unsigned slip_time_elapsed = 0;


    typedef enum {INIT, RESET_CNT, TEST_SH, LOCK, SLIP} state;
    local state curr_state;
    local state next_state;


     function new(string name = "model", uvm_component parent = null);
         super.new(name, parent);

         input_data = new("input_data", this);
         output_data = new("output_data", this);
         reset = new("reset", this);
         curr_state = INIT;
     endfunction: new

    function void do_reset();
        sh_cnt = 0;
        sh_invalid_cnt = 0;
        rx_lock_aquired = 2'b0;
        slip_cmd = 2'b0;
        prev_slip_cmd = 2'b0;
    endfunction

    task run_phase(uvm_phase phase);

        uvm_mvb::sequence_item#(1, 2) tr_input_data;
        uvm_reset::sequence_item tr_reset;

        uvm_logic_vector::sequence_item#(2) tr_output_data;

        forever begin

            input_data.get(tr_input_data);
            reset.get(tr_reset);

            // FSM Next state logic
            case (curr_state)
                INIT : next_state = RESET_CNT;
                RESET_CNT: next_state = TEST_SH;
                TEST_SH : begin
                    if (tr_input_data.src_rdy == 'b1) begin
                        if ((tr_input_data.data[0] == 'b01 || tr_input_data.data[0] == 'b10)) begin
                            if (sh_cnt == SH_CNT_MAX - 1) begin
                                if (sh_invalid_cnt == 0) begin
                                    next_state = LOCK;
                                end else begin
                                    next_state = RESET_CNT;
                                end
                            end
                        end else begin
                            if (sh_invalid_cnt == (SH_INVALID_CNT_MAX - 1) || rx_lock_aquired == 2'b0) begin
                                next_state = SLIP;
                            end else if (sh_cnt == SH_CNT_MAX - 1) begin
                                next_state = RESET_CNT;
                            end
                        end
                    end
                end
                LOCK : next_state = RESET_CNT;
                SLIP : begin
                    next_state = SLIP;
                    if (slip_time_elapsed == SLIP_WAIT_TIME) begin
                        next_state = RESET_CNT;
                        slip_time_elapsed = 0;
                    end
                end
            endcase

            slip_cmd_reg = slip_cmd;

            if (next_state == SLIP && slip_time_elapsed == 0) begin
                slip_time_elapsed = 1;
            end else if (slip_time_elapsed != 0) begin
                slip_time_elapsed = slip_time_elapsed + 1;
            end

            if (curr_state == SLIP) begin
                slip_cmd = 2'b1;
            end else begin
                slip_cmd = 2'b0;
            end

            slip_cmd_out = slip_cmd && !slip_cmd_reg;



            rx_lock_aquired = rx_lock_aquired_reg1;
            if (curr_state == LOCK) begin
                rx_lock_aquired_reg1 = 2'b1;
            end else if (curr_state == INIT || curr_state == SLIP) begin
                rx_lock_aquired_reg1 = 2'b0;
            end


            if (curr_state != RESET_CNT) begin
                if (tr_input_data.src_rdy == 'b1 && curr_state == TEST_SH) begin
                    sh_cnt = sh_cnt + 1;
                    if (!(tr_input_data.data[0] == 'b01 || tr_input_data.data[0] == 'b10)) begin
                        sh_invalid_cnt = sh_invalid_cnt + 1;
                    end
                end
            end else begin
                sh_cnt = 0;
                sh_invalid_cnt = 0;
            end


            if (tr_reset.reset != 2'b0) begin
                curr_state = INIT;
                rx_lock_aquired = 2'b0;
                slip_cmd = 2'b0;
                prev_slip_cmd = 2'b0;
            end else begin
                curr_state = next_state;
            end

            tr_output_data = uvm_logic_vector::sequence_item#(2)::type_id::create("tr_output_data");

            tr_output_data.data[0] = rx_lock_aquired;
            tr_output_data.data[1] = slip_cmd_out;

            output_data.write(tr_output_data);
        end

    endtask
 endclass
