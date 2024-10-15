// rb_transaction.sv: Read Bus transaction
// Copyright (C) 2024 CESNET z. s. p. o.
// Author: Tomas Hak <hak@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

class RbTransaction #(ADDR_WIDTH = 8, FRAGMENTED_MEM = FALSE, ITEMS = 2**ADDR_WIDTH, BLOCK_ITEMS = 20) extends MvbTransaction#(.ITEM_WIDTH(ADDR_WIDTH));
    constraint mem_items_constr { data < ITEMS; }
    // in fragmented mode top BLOCK addresses are not used
    constraint frag_mem_constr { !FRAGMENTED_MEM || data[$clog2(BLOCK_ITEMS)-1 : 0] < BLOCK_ITEMS; }

    virtual function Transaction copy(Transaction to = null);
        RbTransaction #(ADDR_WIDTH, FRAGMENTED_MEM, ITEMS, BLOCK_ITEMS) tr;
        if (to == null)
            tr = new();
        else
            $cast(tr, to);
        copy = super.copy(tr);
    endfunction

endclass
