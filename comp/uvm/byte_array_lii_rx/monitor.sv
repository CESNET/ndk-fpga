/*
 * file       : monitor.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: byte_array to lii_rx monitor
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef TEST_MONITOR_SV
`define TEST_MONITOR_SV

// For RX path of ETH PHY
class monitor_byte_array #(int unsigned DATA_WIDTH, logic DIC_EN, int unsigned VERBOSITY, int unsigned META_WIDTH, int unsigned SOF_WIDTH) extends uvm_byte_array::monitor;

    `uvm_component_param_utils(uvm_byte_array_lii_rx::monitor_byte_array #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, SOF_WIDTH))

    // Analysis port
    uvm_analysis_imp #(uvm_lii_rx::sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH), monitor_byte_array #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, SOF_WIDTH)) analysis_export;
    uvm_byte_array::sequence_item h_tr;
    local byte unsigned tr_data_fifo[$];
    local int BYTE_NUM;

    logic last_chunk  = 1'b0;
    local int sof_pos = 0;

    // Deficit idle count variables
    local int gap_length;
    local int average_gap;
    local bit inframe   = 0;
    local int total_gap = 1;

    // Reference deficit idle count variables
    local int dic             = 0;
    local int ref_gap_length  = 0;
    local int frame_cnt       = 0;
    local int ref_total_gap   = 0;
    local int ref_average_gap = 0;

    function new (string name, uvm_component parent);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
    endfunction

    // Deficit idle count reference algorithm
    function void deficit_idle_count();
        case (dic)
            0:
            begin
                case (h_tr.data.size() % 4)
                    0:
                    begin
                        dic = 0;
                        ref_gap_length = 12;
                    end
                    1:
                    begin
                        dic = 1;
                        ref_gap_length = 11;
                    end
                    2:
                    begin
                        dic = 2;
                        ref_gap_length = 10;
                    end
                    3:
                    begin
                        dic = 3;
                        ref_gap_length = 9;
                    end
                endcase
            end
            1:
            begin
                case (h_tr.data.size() % 4)
                    0:
                    begin
                        dic = 1;
                        ref_gap_length = 12;
                    end
                    1:
                    begin
                        dic = 2;
                        ref_gap_length = 11;
                    end
                    2:
                    begin
                        dic = 3;
                        ref_gap_length = 10;
                    end
                    3:
                    begin
                        dic = 0;
                        ref_gap_length = 13;
                    end
                endcase
            end
            2:
            begin
                case (h_tr.data.size() % 4)
                    0:
                    begin
                        dic = 2;
                        ref_gap_length = 12;
                    end
                    1:
                    begin
                        dic = 3;
                        ref_gap_length = 11;
                    end
                    2:
                    begin
                        dic = 0;
                        ref_gap_length = 14;
                    end
                    3:
                    begin
                        dic = 1;
                        ref_gap_length = 13;
                    end
                endcase
            end
            3:
            begin
                case (h_tr.data.size() % 4)
                    0:
                    begin
                        dic = 3;
                        ref_gap_length = 12;
                    end
                    1:
                    begin
                        dic = 0;
                        ref_gap_length = 15;
                    end
                    2:
                    begin
                        dic = 1;
                        ref_gap_length = 14;
                    end
                    3:
                    begin
                        dic = 2;
                        ref_gap_length = 13;
                    end
                endcase
            end
        endcase

        ref_total_gap += ref_gap_length;
        if (VERBOSITY >= 2) begin
            $write("REF GAP LENGTH: %d \n", ref_gap_length);
        end

    endfunction


    // Deficit idle count
    // DIC_EN - DIC is count only at TX MAC at LII TX interface.
    function void gap_control(uvm_lii_rx::sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH) tr);
        if (DIC_EN == 1'b1) begin
            if (VERBOSITY >= 2) begin
                $write("Transaction data: %h time %t RDY %b SOF %b EOF %b \n", tr.data, $time(), tr.rdy, tr.sof, tr.eof);
            end

            if (tr.rdy == 1'b1 && inframe == 1'b0) begin
                if (|tr.sof && frame_cnt > 0) begin
                    inframe   = 1'b1;
                    total_gap += gap_length;

                    if (VERBOSITY >= 2) begin
                        $write("GAP LENGTH: %d \n", gap_length);
                    end

                    if (gap_length <= 8) begin
                        `uvm_fatal(this.get_full_name(), "Gap between frames is less then minmal value")
                        $write("GAP LENGTH:         %d\n", gap_length);
                        $write("MINIMAL GAP LENGTH: %d\n", 8);
                    end

                    // Count average inter packet gap for 200 frames
                    if ((frame_cnt % 200) == 0 && frame_cnt != 0) begin

                        ref_average_gap = ref_total_gap/frame_cnt;
                        average_gap = total_gap/frame_cnt;

                        if (VERBOSITY >= 3) begin
                            $write("AVERAGE GAP LENGTH:     %d\n", average_gap);
                            $write("REF AVERAGE GAP LENGTH: %d\n", ref_average_gap);
                            $write("FRAME COUNT:            %d\n", frame_cnt);
                            $write("TOTAL GAP:              %d\n", total_gap);
                            $write("REF TOTAL GAP:          %d\n", ref_total_gap);
                        end

                        if (average_gap <= ref_average_gap) begin
                            `uvm_fatal(this.get_full_name(), "Gap between frames is less then average value")
                            $write("AVERAGE GAP LENGTH:     %d\n", average_gap);
                            $write("REF AVERAGE GAP LENGTH: %d\n", ref_average_gap);
                        end
                    end
                end else begin
                    gap_length += (DATA_WIDTH/8);
                end
            end
        end
    endfunction

    // Write 32 transactions to data stream and send it to scoreboard.
    virtual function void write(uvm_lii_rx::sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH) tr);

        gap_control(tr);

        // Write to scoreboard logic
        if (tr.rdy === 1'b1) begin
            sof_pos = 0;
            if(|tr.sof && tr.link_status === 1'b1) begin
                h_tr    = uvm_byte_array::sequence_item::type_id::create("h_tr");
                inframe = 1'b1;
                tr_data_fifo.delete();
                sof_pos = $clog2(int'(tr.sof));
                BYTE_NUM = DATA_WIDTH/8;
            end

            if (inframe == 1'b1) begin
                if (tr.eof == 1'b1) begin
                    if (tr.err == 1'b1) begin
                        BYTE_NUM = DATA_WIDTH/8;
                    end else begin
                        BYTE_NUM = int'(tr.bytes_vld);
                    end
                    last_chunk = 1'b1;
                end
            end

            // Insert data to FIFO
            for (int i = (8*sof_pos); i < BYTE_NUM; i++) begin
                tr_data_fifo.push_back(tr.data[((i+1)*8)-1 -: 8]);
            end

            // Write when the high level transaction is whole.
            if(last_chunk == 1'b1) begin
                h_tr.data = new[tr_data_fifo.size()];
                gap_length = (DATA_WIDTH/8) - tr.bytes_vld;
                deficit_idle_count();
                inframe = 1'b0;
                last_chunk = 1'b0;
                frame_cnt++;
                h_tr.data = tr_data_fifo;
                analysis_port.write(h_tr);
                tr_data_fifo.delete();
            end
        end
    endfunction

endclass

class monitor_logic_vector #(int unsigned DATA_WIDTH, logic DIC_EN, int unsigned VERBOSITY, int unsigned META_WIDTH, int unsigned LOGIC_WIDTH, int unsigned SOF_WIDTH) extends uvm_logic_vector::monitor #(LOGIC_WIDTH);

    `uvm_component_param_utils(uvm_byte_array_lii_rx::monitor_logic_vector #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH))

    // Analysis port
    uvm_analysis_imp #(uvm_lii_rx::sequence_item#(DATA_WIDTH, META_WIDTH, SOF_WIDTH), monitor_logic_vector #(DATA_WIDTH, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)) analysis_export;


    uvm_logic_vector::sequence_item #(LOGIC_WIDTH) h_tr;
    logic inframe = 1'b0;
    logic was_sof = 1'b0;
    logic err_trig = 1'b0;
    logic link_down = 1'b0;
    int frame_cnt = 0;

    function new (string name, uvm_component parent);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
    endfunction

    virtual function void write(uvm_lii_rx::sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH) tr);
        if (tr.rdy == 1'b1) begin
            if (|tr.sof) begin
                inframe  = 1'b1;
                err_trig = 1'b0;
                was_sof  = 1'b1;
            end

            if (inframe == 1'b1) begin
                if (tr.err == 1'b1) begin
                    err_trig = 1'b1;
                end
                if (tr.eof == 1'b1 && tr.link_status == 1'b0) begin
                    link_down = 1'b1;
                end
            end

            if (tr.eof == 1'b1) begin
                was_sof = 1'b0;
            end
        end

        if (tr.crc_vld == 1'b1 && inframe == 1'b1) begin
            h_tr = uvm_logic_vector::sequence_item #(LOGIC_WIDTH)::type_id::create("h_tr");
            h_tr.data[0] = link_down;       // Link status trigger
            h_tr.data[1] = err_trig;        // Error trigger
            h_tr.data[2] = tr.crc_ok;       // CRC OK
            h_tr.data[3] = tr.crc_vld;      // CRC VLD
            frame_cnt++;
            if (tr.crc_ok == 1'b0 && VERBOSITY == 1) begin
                $write("Bad CRC in monitor %t\n", $time);
            end
            if (was_sof == 1'b1) begin
                inframe  = 1'b1;
            end else begin
                inframe = 1'b0;
            end
            err_trig = 1'b0;
            link_down = 1'b0;
            analysis_port.write(h_tr);
        end
    endfunction
endclass


`endif
