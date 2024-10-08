/*!
* \file custom_trans.sv
* \brief Custom transaction
* author: Jakub Cabal <cabal@cesnet.cz>
* date: 2018
*/
/*
* Copyright (C) 2018 CESNET z. s. p. o.
*
* LICENSE TERMS
*
 * SPDX-License-Identifier: BSD-3-Clause
*
*/

import sv_common_pkg::*;

class CustomTransaction #(MVB_ITEM_WIDTH = 4, ITEM_WIDTH = 8, META_WIDTH = 1) extends Transaction;

    rand bit [MVB_ITEM_WIDTH-1 : 0] hdr;
    rand bit payload = 0;
    rand bit [ITEM_WIDTH-1 : 0] data[];
    rand bit [META_WIDTH-1 : 0] meta;
    bit switch = 0;
    int dataSizeMax = 256;
    int dataSizeMin = 32;
    int switchRate = 80;
    int payloadRate = 80;

    constraint c1 {
        payload dist {1 := payloadRate, 0 := (100-payloadRate)};
        data.size inside {[dataSizeMin:dataSizeMax]};
    };

    virtual function void display(string prefix = "");
        if(prefix != "") begin
            $write("---------------------------------------------------------");
            $write("-- %s\n",prefix);
            $write("---------------------------------------------------------");
        end
        $write("HDR: 0x%h\n", hdr);
        $write("SWITCH: %1b\n", switch);
        $write("PAYLOAD: %1b\n", payload);
        $write("SIZE: %d\n",data.size());
        $write("META: 0x%h\n", meta);
        if (payload) begin
            $write("DATA SIZE: %1d ITEMS, DATA:", data.size);
            for (int j=0; j < data.size; j++) begin
                if (j%8==0) $write("\n\t");
                if (j%8==0) $write(" ");
                $write("%x ",data[j]);
            end
            $write("\n");
        end
        $write("\n");
    endfunction

    virtual function Transaction copy(Transaction to = null);
        CustomTransaction #(MVB_ITEM_WIDTH,ITEM_WIDTH,META_WIDTH) tr;

        if (to == null)
            tr = new();
        else
            $cast(tr, to);

        tr.hdr = hdr;
        tr.switch = switch;
        tr.payload = payload;
        tr.data = data;
        tr.meta = meta;
        tr.dataSizeMax = dataSizeMax;
        tr.dataSizeMin = dataSizeMin;
        copy = tr;
    endfunction

    virtual function bit compare(input Transaction to, output string diff, input int kind = -1);
        CustomTransaction #(MVB_ITEM_WIDTH,ITEM_WIDTH,META_WIDTH) tr;
        $cast(tr, to);

        if (hdr != tr.hdr) begin
            //$write("Header does not match!\n");
            return 0;
        end
        if (switch != tr.switch) begin
            //$write("Switch does not match!\n");
            return 0;
        end
        if (payload != tr.payload) begin
            //$write("Payload does not match!\n");
            return 0;
        end
        if (payload) begin
            if (meta != tr.meta) begin
                //$write("Metadata does not match!\n");
                return 0;
            end
            if (data != tr.data) begin
                if (data.size != tr.data.size) begin
                    //$write("Data size does not match!\n");
                end else begin
                    for (int j=0; j < data.size; j++) begin
                        if (data[j] != tr.data[j]) begin
                            //$write("Data items #%1d does not match!\n", j);
                            break;
                        end
                    end
                end
                return 0;
            end
        end

        return 1;
    endfunction

endclass
