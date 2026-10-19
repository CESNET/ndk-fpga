// sequence_tb.sv: Meta {META, TS} sequence
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

// Generates extended meta transactions, one per packet:
//   [EXTENDED_META_WIDTH-1:TS_WIDTH] = random META
//   [TS_WIDTH-1:0]                   = TIMESTAMP
//
// Each timestamp step is random in [ts_min:ts_max] (the bounds are slightly
// preferred). The step is used as follows:
//   TS_FORMAT = 0 (interval): TIMESTAMP = step (delay since the previous packet)
//   TS_FORMAT = 1 (absolute): TIMESTAMP = start_value + sum of steps (strictly
//                             increasing; ts_abs_max is a sanity bound)
//
// All knobs are set by the virtual sequence before start().
class sequence_meta #(
    int unsigned META_WIDTH,
    int unsigned TS_WIDTH,
    int unsigned EXTENDED_META_WIDTH,
    int unsigned TS_FORMAT
) extends uvm_sequence #(uvm_logic_vector::sequence_item #(EXTENDED_META_WIDTH));
    `uvm_object_param_utils(uvm_packet_delayer::sequence_meta #(META_WIDTH, TS_WIDTH, EXTENDED_META_WIDTH, TS_FORMAT))

    int unsigned         transaction_count = 1;
    int unsigned         ts_min            = 1;
    int unsigned         ts_max            = 1;
    int unsigned         ts_abs_max        = (1 << (TS_WIDTH-1)) - 1;
    // TS_FORMAT = 1: first accumulator value (a phase after TIME_RESET restarts low)
    logic [TS_WIDTH-1:0] start_value       = '0;

    function new(string name = "sequence_meta");
        super.new(name);
    endfunction

    task body;
        logic [TS_WIDTH-1:0] ts_acc;
        logic [TS_WIDTH-1:0] ts_step;
        logic [TS_WIDTH-1:0] ts_val;

        req    = uvm_logic_vector::sequence_item #(EXTENDED_META_WIDTH)::type_id::create("req");
        ts_acc = start_value;

        for (int unsigned it = 0; it < transaction_count; it++) begin
            if (!std::randomize(ts_step) with {
                    ts_step dist {
                        ts_min          :/ 1,
                        [ts_min:ts_max] :/ 10,
                        ts_max          :/ 1
                    };
                }) begin
                `uvm_fatal(get_type_name(), $sformatf("Timestamp randomize() failed (ts_min=%0d, ts_max=%0d)",
                           ts_min, ts_max))
            end

            if (TS_FORMAT == 1) begin
                ts_acc = ts_acc + ts_step;
                ts_val = ts_acc;
                if (int'(ts_val) > ts_abs_max) begin
                    `uvm_fatal(get_type_name(), $sformatf("Absolute timestamp %0d exceeds ts_abs_max=%0d",
                               ts_val, ts_abs_max))
                end
            end else begin
                ts_val = ts_step;
            end

            start_item(req);
            req.randomize();                 // random META
            req.data[TS_WIDTH-1:0] = ts_val; // TIMESTAMP
            finish_item(req);

            `uvm_info(get_type_name(), $sformatf("Generated TS[%0d] = %0d", it, int'(ts_val)), UVM_LOW)
        end
    endtask

endclass
