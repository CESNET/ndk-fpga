/*!
 * \file mfb_transaction.sv
 * \brief Multi-Frame Bus transaction
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 */



class MfbTransaction #(ITEM_WIDTH = 8, META_WIDTH = 1) extends Transaction;

    int frameSizeMax = 1518;
    int frameSizeMin = 60;

    int sof = 0;
    int sof_pos = 0;

    rand bit [META_WIDTH-1 : 0] meta;
    rand bit [ITEM_WIDTH-1 : 0] data[];

    bit check_meta = 0;

    constraint c1 {
        data.size inside {[frameSizeMin:frameSizeMax]};
    };


    virtual function void display(string prefix = "");
        if(prefix != "") begin
            $write("---------------------------------------------------------\n");
            $write("-- %s\n",prefix);
            $write("---------------------------------------------------------\n");
        end
        $write("Frame SOF: %1d \n", sof);
        $write("Frame SOF_POS: %1d \n", sof_pos);
        // uncommented if you need see frame metadata
        $write("Frame metadata: %x \n", meta);
        $write("Frame size: %1d items, Data:", data.size);
        for(int j=0; j < data.size; j++) begin
            if(j%32==0) $write("\n\t");
            if(j%8==0) $write(" ");
            $write("%x ",data[j]);
        end
        $write("\n");
    endfunction

    virtual function Transaction copy(Transaction to = null);
        MfbTransaction #(ITEM_WIDTH,META_WIDTH) tr;
        if (to == null)
            tr = new();
        else
            $cast(tr, to);
        tr.data = data;
        tr.meta = meta;
        tr.check_meta = check_meta;
        tr.sof = sof;
        tr.sof_pos = sof_pos;
        tr.frameSizeMax = frameSizeMax;
        tr.frameSizeMin = frameSizeMin;
        copy = tr;
    endfunction

    virtual function bit compare(input Transaction to, output string diff, input int kind = -1);
        MfbTransaction #(ITEM_WIDTH,META_WIDTH) tr;
        $cast(tr, to);
        if(data != tr.data) begin
            if(data.size != tr.data.size)
                diff = "size of data does not match";
            else
                for(int j=0; j < data.size; j++)
                    if(data[j] != tr.data[j]) begin
                        diff = $sformatf("Items #%1d does not match", j);
                        break;
                    end
            return 0;
        end else begin
            if((check_meta == 1'b1 || tr.check_meta == 1'b1) && meta != tr.meta) begin
                diff = "Metadata does not match";
                return 0;
            end
            else begin
                return 1;
            end
        end
    endfunction

endclass
