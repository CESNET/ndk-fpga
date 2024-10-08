/*!
 * \file mvb_transaction.sv
 * \brief Multi-Value Bus transaction
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



class MvbTransaction #(ITEM_WIDTH = 8) extends Transaction;

    rand bit [ITEM_WIDTH-1 : 0] data;
    int unsigned stream;
    int unsigned word;


    virtual function void display(string prefix = "");
        if(prefix != "") begin
            $write("---------------------------------------------------------\n");
            $write("-- %s\n",prefix);
            $write("---------------------------------------------------------\n");
        end
        $write("Value: 0x%1h\n", data);
    endfunction

    virtual function Transaction copy(Transaction to = null);
        MvbTransaction #(ITEM_WIDTH) tr;
        if (to == null)
            tr = new();
        else
            $cast(tr, to);
        tr.data = data;
        tr.stream = stream;
        tr.word = word;
        copy = tr;
    endfunction

    virtual function bit compare(input Transaction to, output string diff, input int kind = -1);
        MvbTransaction #(ITEM_WIDTH) tr;
        $cast(tr, to);
        return data == tr.data;
    endfunction

endclass
