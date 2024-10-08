// wb_transaction.sv: Write Bus transaction
// Copyright (C) 2023 CESNET z. s. p. o.
// Author: Tomas Fukac <fukac@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

class WbTransaction #(DATA_WIDTH = 64, ADDR_WIDTH = 8, FRAGMENTED_MEM = FALSE) extends Transaction;

    rand bit [DATA_WIDTH-1 : 0] data;
    rand bit [DATA_WIDTH-1 : 0] mask;
    rand bit [ADDR_WIDTH-1 : 0] addr;

    // in fragmented mode MLAB addresses 21-32 are not used
    constraint frag_mem_constr { addr[4 : 0] < 20 || !FRAGMENTED_MEM; }

    virtual function void display(string prefix = "");
        if(prefix != "") begin
            $write("---------------------------------------------------------\n");
            $write("-- %s\n",prefix);
            $write("---------------------------------------------------------\n");
        end
        $write("DATA: 0x%1h\n", data);
        $write("MASK: 0x%1h\n", mask);
        $write("ADDR: 0x%1h\n", addr);
    endfunction

    virtual function Transaction copy(Transaction to = null);
        WbTransaction #(DATA_WIDTH, ADDR_WIDTH, FRAGMENTED_MEM) tr;
        if(to == null) begin
            tr = new();
        end else begin
            $cast(tr, to);
        end
        tr.data = data;
        tr.mask = mask;
        tr.addr = addr;
        copy = tr;
    endfunction

    virtual function bit compare(input Transaction to, output string diff, input int kind = -1);
        WbTransaction #(DATA_WIDTH, ADDR_WIDTH, FRAGMENTED_MEM) tr;
        $cast(tr, to);
        // TODO!!!
        return data == tr.data;
    endfunction

endclass
