/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
 */

class transaction  extends sv_common_pkg::Transaction;

    ///////////////////////////////////
    // random transaction variables
    logic [256-1:0]  data;
    logic [128-1:0]  hdr;
    logic [32-1:0]   prefix;
    logic            sop;
    logic            eop;

    ///////////////////////////////////
    // copy, compare, convert to string function
    function new ();
    endfunction

    virtual function sv_common_pkg::Transaction copy(sv_common_pkg::Transaction to = null);
        transaction rhs;

        if(to == null) begin
            rhs = new();
        end else begin
            $cast(rhs, to);
        end

        rhs.data = data;
        rhs.hdr  = hdr;
        rhs.prefix = prefix;
        rhs.sop    = sop;
        rhs.eop    = eop;
        return rhs;
    endfunction

    virtual function bit compare(input sv_common_pkg::Transaction to, output string diff, input int kind = -1);
        bit result = 1'b1;
        transaction tr;
        $cast(tr, to);

        result &= (data === tr.data);
        result &= (hdr  === tr.hdr);
        result &= (prefix === tr.prefix);
        result &= (sop  === tr.sop);
        result &= (eop  === tr.eop);
        return result;
    endfunction

    virtual function void display(string prefix = "");
        if(prefix != "") begin
            $write("---------------------------------------------------------\n");
            $write("-- %s\n",prefix);
            $write("---------------------------------------------------------\n");
        end
        $write("\tDATA : %h\n\tHDR : %h\n\tPrefix : %h\n\tsop %h eop %h\n",
                data, hdr, this.prefix, sop, eop);
    endfunction
endclass

