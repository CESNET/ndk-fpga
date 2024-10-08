//-- sequence.sv
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequence_meta#(META_WIDTH, TIMESTAMP_WIDTH, TIMESTAMP_MIN, TIMESTAMP_MAX, TIMESTAMP_FORMAT, QUEUES) extends uvm_sequence #(uvm_logic_vector::sequence_item#(META_WIDTH));
    `uvm_object_param_utils(uvm_timestamp_limiter::sequence_meta#(META_WIDTH, TIMESTAMP_WIDTH, TIMESTAMP_MIN, TIMESTAMP_MAX, TIMESTAMP_FORMAT, QUEUES))

    regmodel#(QUEUES) m_regmodel;

    function new(string name = "sequence_meta");
        super.new(name);
    endfunction

    task body;
        localparam QUEUES_W = (QUEUES > 1) ? $clog2(QUEUES) : 1        ;
        logic [TIMESTAMP_WIDTH-1 : 0] timestamp[QUEUES] = '{default:'0};
        logic [TIMESTAMP_WIDTH-1 : 0] ts_step           = 0            ;
        logic [$clog2(QUEUES) -1 : 0] mfb_queue         = 0            ;
        time                          run_time_min      = 30us         ;
        time                          run_time_max      = 500us          ;
        time                          start_time        = 0            ;
        time                          run_time                         ;
        uvm_status_e                  status                           ;

        forever begin
            if (TIMESTAMP_FORMAT) begin
                if (start_time == 0) begin
                    start_time = $time();
                    assert(std::randomize(run_time) with {run_time inside {[run_time_min:run_time_max]};});
                    m_regmodel.m_rst_q.write(status, 'h1, .parent(this));
                    timestamp = '{default:'0};
                    #(100ns);
                end
                if ($time > (start_time + run_time)) begin
                    assert(std::randomize(run_time) with {run_time inside {[run_time_min:run_time_max]};});
                    m_regmodel.m_rst_q.write(status, 'h1, .parent(this));
                    timestamp = '{default:'0};
                    #(100ns);
                    start_time = $time();
                end
            end
            assert(std::randomize(ts_step) with {
                    ts_step inside {[TIMESTAMP_MIN : TIMESTAMP_MAX]};
                });
            `uvm_do_with(req, {
                if (TIMESTAMP_FORMAT == 0) {
                    data[TIMESTAMP_WIDTH-1 : 0] inside {[TIMESTAMP_MIN : TIMESTAMP_MAX]};
                } else {
                    if (QUEUES > 1) {
                        data[TIMESTAMP_WIDTH-1 : 0] == timestamp[int'(data[TIMESTAMP_WIDTH+QUEUES_W-1 : TIMESTAMP_WIDTH])];
                    } else {
                        data[TIMESTAMP_WIDTH-1 : 0] == timestamp[0];
                    }
                }
            });
            if (QUEUES != 1) begin
                mfb_queue = req.data[TIMESTAMP_WIDTH+QUEUES_W-1 : TIMESTAMP_WIDTH];
            end
            timestamp[int'(mfb_queue)] += ts_step;
        end
    endtask
endclass
