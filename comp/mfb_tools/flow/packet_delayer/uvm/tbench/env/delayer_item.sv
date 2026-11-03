// delayer_item.sv: Sequence items carrying the expected packet release time
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause
//
// The reference model stores the predicted release time in expected_release.
// It is a standalone field (not in start[]) so it does not affect the base
// class time_last() used by the comparer watchdogs.

// Extended data item: plain data array + expected release time (EOF)
class delayer_data_item #(int unsigned ITEM_WIDTH) extends uvm_logic_vector_array::sequence_item #(ITEM_WIDTH);
    `uvm_object_param_utils(uvm_packet_delayer::delayer_data_item #(ITEM_WIDTH))

    // Expected release time (data monitor stamps the EOF)
    time expected_release = 0ns;

    function new(string name = "delayer_data_item");
        super.new(name);
    endfunction

    virtual function void do_copy(uvm_object rhs);
        delayer_data_item #(ITEM_WIDTH) rhs_;

        if (!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_copy:", "Failed to cast transaction object.")
            return;
        end
        // Copies data via super.do_copy
        super.do_copy(rhs);
        expected_release = rhs_.expected_release;
    endfunction

    // expected_release is checked by the time-aware comparer, not do_compare

    function string convert2string();
        return {super.convert2string(),
                $sformatf("\n\texpected release = %0t", expected_release)};
    endfunction
endclass

// Extended meta item: plain metadata + expected release time (SOF)
class delayer_meta_item #(int unsigned META_WIDTH) extends uvm_logic_vector::sequence_item #(META_WIDTH);
    `uvm_object_param_utils(uvm_packet_delayer::delayer_meta_item #(META_WIDTH))

    // Expected release time (meta monitor stamps the SOF)
    time expected_release = 0ns;

    function new(string name = "delayer_meta_item");
        super.new(name);
    endfunction

    virtual function void do_copy(uvm_object rhs);
        delayer_meta_item #(META_WIDTH) rhs_;

        if (!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_copy:", "Failed to cast transaction object.")
            return;
        end
        super.do_copy(rhs);
        expected_release = rhs_.expected_release;
    endfunction

    // expected_release is checked by the time-aware comparer, not do_compare

    function string convert2string();
        return {super.convert2string(),
                $sformatf("\n\texpected release = %0t", expected_release)};
    endfunction
endclass
