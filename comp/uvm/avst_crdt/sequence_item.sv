// sequence_item.sv: Item for AVST credit control sequencer
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_item #(int unsigned UPDATE_CNT_WIDTH) extends uvm_common::sequence_item;
    `uvm_object_param_utils(uvm_avst_crdt::sequence_item #(UPDATE_CNT_WIDTH))

    // ------------------------------- //
    // Bus structure of credit control //
    // ------------------------------- //

    rand logic                          init;
    rand logic                          init_ack;
    rand logic                          update;
    rand logic [UPDATE_CNT_WIDTH-1 : 0] update_cnt;

    // Constructor
    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    // -------------------- //
    // Common UVM functions //
    // -------------------- //

    function void do_copy(uvm_object rhs);
        sequence_item #(UPDATE_CNT_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal(this.get_full_name(), "Failed to cast transaction object.")
            return;
        end

        // Item copying
        super.do_copy(rhs);
        init       = rhs_.init;
        init_ack   = rhs_.init_ack;
        update     = rhs_.update;
        update_cnt = rhs_.update_cnt;
    endfunction

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item #(UPDATE_CNT_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        // Item comparison
        return (
            super.do_compare(rhs, comparer ) &&
            (init       === rhs_.init      ) &&
            (init_ack   === rhs_.init_ack  ) &&
            (update     === rhs_.update    ) &&
            (update_cnt === rhs_.update_cnt)
        );

    endfunction

    function string convert2string();
        string output_string = "";

        // Item stringifying
        $sformat(output_string, {"\n\tINIT %0b\n\tINIT_ACK %0b\n\tUPDATE %0b\n\tUPDATE_CNT %0h\n"},
            init,
            init_ack,
            update,
            update_cnt
        );

        return output_string;
    endfunction

endclass
