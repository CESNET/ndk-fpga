// credit_item.sv: Item of AVST credit
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class credit_item extends uvm_sequence_item;
    `uvm_object_utils(uvm_pcie_intel_r_tile::credit_item)

    // ---------- //
    // Properties //
    // ---------- //

    rand logic        init;
    rand logic        init_ack;
    rand logic        update;
    rand int unsigned update_cnt;

    // Constructor
    function new(string name = "credit_item");
        super.new(name);
    endfunction

    // -------------------- //
    // Common UVM functions //
    // -------------------- //

    function void do_copy(uvm_object rhs);
        credit_item rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal(this.get_full_name(), "Failed to cast transaction object")
            return;
        end

        super.do_copy(rhs);
        init       = rhs_.init;
        init_ack   = rhs_.init_ack;
        update     = rhs_.update;
        update_cnt = rhs_.update_cnt;
    endfunction

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        credit_item rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal(this.get_full_name(), "Failed to cast transaction object")
            return 0;
        end

        return (
            super.do_compare(rhs, comparer) &&
            (init       === rhs_.init      ) &&
            (init_ack   === rhs_.init_ack  ) &&
            (update     === rhs_.update    ) &&
            (update_cnt ==  rhs_.update_cnt)
        );
    endfunction

    function string convert2string();
        string output_string;

        output_string = $sformatf("\n\tINIT %0b\n\tINIT_ACK %0b\n\tUPDATE %0b\n\tUPDATE_CNT %0d\n",
            init,
            init_ack,
            update,
            update_cnt
        );

        return output_string;
    endfunction

endclass
