// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>
// SPDX-License-Identifier: BSD-3-Clause

// This low level sequence define bus functionality
class sequence_rx_base #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_common::sequence_base#(config_sequence, uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH));

    `ndk_object_param_utils(
        uvm_vector2packet::sequence_rx_base #(ITEMS, ITEM_WIDTH, TUSER_WIDTH),
        $sformatf("uvm_vector2packet::sequence_rx_base#(%0d,%0d,%0d)", ITEMS, ITEM_WIDTH, TUSER_WIDTH)
    )

    rand int unsigned rdy_probability;

    rand int unsigned frame_num;
    rand int unsigned frame_size_min;
    rand int unsigned frame_size_max;

    rand int unsigned space_size_min;
    rand int unsigned space_size_max;

    constraint c_space_size {
        space_size_min <= space_size_max;
        space_size_min dist {
             cfg.space_size_min :/ 5,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*0 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*1] :/ 20,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*1 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*2] :/ 7,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*2 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*3] :/ 5,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*3 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*4] :/ 3,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*4 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*5] :/ 2,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*5 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*6] :/ 1,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*6 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*7] :/ 1,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*7 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*8] :/ 3,
             cfg.space_size_max :/ 5
        };

        space_size_max dist {
             cfg.space_size_min :/ 5,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*0 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*1] :/ 20,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*1 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*2] :/ 7,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*2 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*3] :/ 5,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*3 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*4] :/ 3,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*4 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*5] :/ 2,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*5 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*6] :/ 1,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*6 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*7] :/ 1,
             // verilog_lint: waive line-length
            [cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*7 : cfg.space_size_min + (cfg.space_size_max-cfg.space_size_min)/8*8] :/ 3,
             cfg.space_size_max :/ 5
        };
    }

    constraint c_frame_size {
        frame_num inside {[1:1000]};
        frame_size_min <= frame_size_max;
        frame_size_min dist {
             cfg.frame_size_min :/ 5,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*0 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*1] :/ 20,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*1 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*2] :/ 7,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*2 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*3] :/ 5,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*3 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*4] :/ 3,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*4 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*5] :/ 2,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*5 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*6] :/ 1,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*6 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*7] :/ 1,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*7 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*8] :/ 7,
             cfg.frame_size_max :/ 5
        };

        frame_size_max dist {
             cfg.frame_size_min :/ 5,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*0 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*1] :/ 20,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*1 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*2] :/ 7,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*2 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*3] :/ 5,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*3 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*4] :/ 3,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*4 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*5] :/ 2,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*5 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*6] :/ 1,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*6 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*7] :/ 1,
             // verilog_lint: waive line-length
            [cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*7 : cfg.frame_size_min + (cfg.frame_size_max-cfg.frame_size_min)/8*8] :/ 7,
             cfg.frame_size_max :/ 5
        };
    }

    constraint c_rdy_probability {
        rdy_probability != 0;
        rdy_probability dist {
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*0 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*1] :/ 3,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*1 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*2] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*2 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*3] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*3 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*4] :/ 1,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*4 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*5] :/ 3,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*5 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*6] :/ 5,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*6 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*7] :/ 10,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*7 : cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)/8*8] :/ 20,
             cfg.rdy_probability_max :/ 30
        };
    }

    function new(string name = "uvm_vector2packet::sequence_rx_base");
        super.new(name);
    endfunction

    task body;
        int unsigned frame_size;
        int unsigned space_size;

        if (cfg == null) begin
            cfg = new();
        end

        req = uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH)::type_id::create("req", m_sequencer);
        for (int unsigned it = 0; it < frame_num; it++) begin

            std::randomize(frame_size) with {frame_size inside {[frame_size_min:frame_size_max]};};
            std::randomize(space_size) with {space_size inside {[space_size_min:space_size_max]};};

            // SEND FRAMES
            while (frame_size > ITEMS) begin
                start_item(req);
                assert(req.randomize() with {
                        req.tvalid dist {1'b1 :/ rdy_probability, 1'b0 :/ (100-rdy_probability)};
                        req.tvalid == 1'b1 -> (req.tlast == 0);
                        req.tvalid == 1'b1 -> (req.tkeep == '1);
                }) else begin
                    `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize request");
                end
                finish_item(req);
                //dont care
                get_response(rsp);
                if (req.tvalid == 1'b1 && rsp.tready == 1'b1) begin
                    frame_size -= ITEMS;
                end
            end

            // SEND LAST FRAME FRAMES
            do begin
                logic [ITEMS-1:0] tkeep_last;

                tkeep_last = 0;
                for(int unsigned jt = 0; jt < frame_size; jt++) begin
                    tkeep_last[jt] = 1;
                end

                start_item(req);
                assert(req.randomize() with {
                        req.tvalid dist {1'b1 :/ rdy_probability, 1'b0 :/ (100-rdy_probability)};
                        req.tvalid == 1'b1 -> (req.tlast == 1);
                        req.tvalid == 1'b1 -> (req.tkeep == tkeep_last);
                }) else begin
                    `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize request");
                end
                finish_item(req);
                //dont care
                get_response(rsp);
            end while(req.tvalid == 1'b1 && rsp.tready == 1'b1);


            // SEND SPACES
            for (int unsigned jt = 0; jt < space_size; jt++) begin
                start_item(req);
                assert(req.randomize() with {req.tvalid == 1'b0;}) else begin
                    `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize request");
                end
                finish_item(req);
                //dont care
                get_response(rsp);
            end
        end
    endtask
endclass
