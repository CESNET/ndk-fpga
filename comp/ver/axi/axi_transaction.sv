/*!
 * \file mfb_transaction.sv
 * \brief Multi-Frame Bus transaction
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

class AxiTransaction #(ITEM_WIDTH = 8) extends Transaction;

    int frameSizeMin = 1;
    int frameSizeMax = 512;

    rand bit [ITEM_WIDTH-1 : 0] data[];
    logic [3:0] fbe;
    logic [3:0] lbe;

    constraint c1 {
        data.size inside {[frameSizeMin:frameSizeMax]};
    };

    virtual function void display(string prefix = "");
        if(prefix != "") begin
            $write("---------------------------------------------------------\n");
            $write("-- %s\n",prefix);
            $write("---------------------------------------------------------\n");
        end
        $write("fbe: %h lbe %h\n", fbe, lbe);
        $write("Frame size: %1d items, Data:", data.size);
        for(int j=0; j < data.size; j++) begin
            if(j%32==0) $write("\n\t");
            if(j%8==0) $write(" ");
            $write("%x ",data[j]);
        end
        $write("\n");
    endfunction

    virtual function Transaction copy(Transaction to = null);
        AxiTransaction #(ITEM_WIDTH) tr;

        if (to == null)
            tr = new();
        else
            $cast(tr, to);

        tr.fbe  = fbe;
        tr.lbe  = lbe;
        tr.data = data;
        tr.frameSizeMax = frameSizeMax;
        tr.frameSizeMin = frameSizeMin;
        return tr;
    endfunction

    virtual function bit compare(input Transaction to, output string diff, input int kind = -1);
        AxiTransaction #(ITEM_WIDTH) tr;
        $cast(tr, to);
        if (lbe != tr.lbe || fbe != tr.fbe) begin
            return 0;
        end

        if(data != tr.data) begin
            if(data.size != tr.data.size)
                diff = "size does not match";
            else
                for(int j=0; j < data.size; j++)
                    if(data[j] != tr.data[j]) begin
                        diff = $sformatf( "Items #%1d does not match", j);
                        break;
                    end
            return 0;
        end else
            return 1;
    endfunction

endclass

