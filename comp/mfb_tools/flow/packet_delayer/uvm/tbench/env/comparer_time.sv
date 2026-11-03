// comparer_time.sv: Time-aware ordered comparer for the packet delayer
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause
//
// Extends the ordered comparer with a bit-exact time check: the release time
// must equal the expected time. MODEL items carry the expected release time,
// DUT items are plain monitor items (time_last() = observed time).

// General time-aware comparer (MODEL_ITEM and DUT_ITEM may differ)
virtual class time_ordered_cmp_base #(
    type MODEL_ITEM,
    type DUT_ITEM
) extends uvm_common::comparer_base_ordered #(MODEL_ITEM, DUT_ITEM);

    // Explicit statistics (base keeps only the combined `errors`)
    int unsigned time_errors;
    int unsigned data_errors;

    // 1 = compare release time (paced test); 0 = data-only (overload test)
    bit time_check_enable = 1;

    // Time statistics over all matched packets (max_delta = worst late delta)
    longint signed max_delta;
    longint signed total_delta;
    int unsigned   delta_count;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        time_errors = 0;
        data_errors = 0;
        max_delta   = 0;
        total_delta = 0;
        delta_count = 0;
    endfunction

    // Accessors provided by the concrete subclasses
    pure virtual function bit  data_compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
    pure virtual function time expected_get(MODEL_ITEM tr_model);
    pure virtual function time actual_get  (DUT_ITEM   tr_dut);

    // Format a signed delta (in simulation time units) for messages in ns
    function string delta2string(longint signed d);
        real d_ns = real'(d) / real'(1ns);

        if (d < 0) begin
            return $sformatf("-%0gns", -d_ns);
        end else begin
            return $sformatf("+%0gns", d_ns);
        end
    endfunction

    // Data equality AND time conformance
    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        time           t_expected;
        time           t_actual;
        longint signed delta;
        bit            ok = 1;

        t_expected = expected_get(tr_model);
        t_actual   = actual_get(tr_dut);
        delta      = longint'(t_actual) - longint'(t_expected);

        // Bit-exact data comparison
        if (!data_compare(tr_model, tr_dut)) begin
            data_errors++;
            ok = 0;
        end

        // Exact time comparison (skipped when disabled)
        if (time_check_enable) begin
            if (delta != 0) begin
                time_errors++;
                ok = 0;
            end
        end

        // Time statistics
        delta_count++;
        total_delta += delta;
        if (delta > max_delta) begin
            max_delta = delta;
        end

        if (ok) begin
            `uvm_info(this.get_full_name(), $sformatf(
                      "\n\tTime-match %0d: expected %0t, actual %0t, delta %s",
                      compared, t_expected, t_actual, delta2string(delta)),
                      UVM_LOW);
        end else begin
            `uvm_warning(this.get_full_name(), $sformatf(
                         {"\n\tTime/data mismatch %0d:\n\texpected %0t, actual %0t, delta %s",
                          "\nMODEL ITEM : %s\nDUT ITEM   : %s\n"},
                         compared, t_expected, t_actual, delta2string(delta),
                         model_item2string(tr_model), dut_item2string(tr_dut)));
        end

        return ok;
    endfunction

    // success() also accounts for the explicit time/data counters
    virtual function int unsigned success();
        return ((errors == 0) && (time_errors == 0) && (data_errors == 0));
    endfunction

    // Maximum observed late delta
    function longint signed max_delta_get();
        return max_delta;
    endfunction

    function int unsigned time_errors_get();
        return time_errors;
    endfunction

    function int unsigned data_errors_get();
        return data_errors;
    endfunction

    virtual function string info(logic data = 0);
        string        msg;
        longint signed avg;

        avg = (delta_count != 0) ? (total_delta / delta_count) : 0;

        msg = $sformatf(
            {"\n\tErrors %0d Compared %0d (time errors %0d, data errors %0d)",
             "\n\tWait for transaction DUT(%0d) MODEL(%0d)",
             "\n\tMax time delta %s, avg time delta %s"},
            errors, compared, time_errors, data_errors,
            dut_items.size(), model_items.size(),
            delta2string(max_delta), delta2string(avg));

        if (data == 1) begin
            for (int unsigned it = 0; it < model_items.size(); it++) begin
                msg = {msg, $sformatf("\n\nModels transaction : %0d", it), model_item2string(model_items[it])};
            end
            msg = {msg, "\n\n"};
            for (int unsigned it = 0; it < dut_items.size(); it++) begin
                msg = {msg, $sformatf("\n\nDUT transactions : %0d", it), dut_item2string(dut_items[it])};
            end
        end

        return msg;
    endfunction
endclass

// Data-stream comparer (MODEL = extended data item, DUT = plain array item)
class cmp_time_data #(
    int unsigned ITEM_WIDTH
) extends time_ordered_cmp_base #(
    uvm_packet_delayer::delayer_data_item #(ITEM_WIDTH),
    uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)
);
    `uvm_component_param_utils(uvm_packet_delayer::cmp_time_data #(ITEM_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function bit data_compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        return tr_dut.data === tr_model.data;
    endfunction

    virtual function time expected_get(MODEL_ITEM tr_model);
        return tr_model.expected_release;
    endfunction

    virtual function time actual_get(DUT_ITEM tr_dut);
        return tr_dut.time_last();
    endfunction
endclass

// Meta-stream comparer (MODEL = extended meta item, DUT = plain logic_vector item)
class cmp_time_meta #(
    int unsigned META_WIDTH
) extends time_ordered_cmp_base #(
    uvm_packet_delayer::delayer_meta_item #(META_WIDTH),
    uvm_logic_vector::sequence_item #(META_WIDTH)
);
    `uvm_component_param_utils(uvm_packet_delayer::cmp_time_meta #(META_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function bit data_compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        return (tr_model.data === tr_dut.data);
    endfunction

    virtual function time expected_get(MODEL_ITEM tr_model);
        return tr_model.expected_release;
    endfunction

    virtual function time actual_get(DUT_ITEM tr_dut);
        return tr_dut.time_last();
    endfunction
endclass
