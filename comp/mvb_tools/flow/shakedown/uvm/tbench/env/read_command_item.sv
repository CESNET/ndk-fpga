// read_command_item.sv: Read command item
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class read_command_item #(int unsigned TX_ITEMS) extends uvm_common::uvm_sequence_item;
    `uvm_object_param_utils(uvm_mvb_shakedown::read_command_item #(TX_ITEMS))

    bit [TX_ITEMS-1 : 0] read;

    // Constructor
    function new(string name = "read_command_item");
        super.new(name);
    endfunction

    // -------------------- //
    // Common UVM functions //
    // -------------------- //

    // Properly copies all transaction attributes
    function void do_copy(uvm_object rhs);
        read_command_item #(TX_ITEMS) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_copy:", "Failed to cast transaction object.")
            return;
        end

        // Copy all attributes
        read = rhs_.read;
    endfunction

    // Properly compares all transaction attributes representing output pins
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        read_command_item #(TX_ITEMS) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        // Compare all attributes that maters
        return (
            (super.do_compare(rhs, comparer)) &&
            (read === rhs_.read)
        );
    endfunction

    // Visualize the sequence item to string
    function string convert2string();
        string output_string;

        output_string = $sformatf("%s\n\tread: 0b%0b \n", super.convert2string(), read);

        return output_string;
    endfunction

endclass
