/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/


class transaction extends sv_common_pkg::Transaction;

     //data vrite to bus
     // emtpy data => driver send empty transaction!!
    rand logic [256-1:0] data;
    rand logic [128-1:0] hdr;
    rand logic [32-1:0]  prefix;
    rand logic [1-1:0]   sop;
    rand logic [1-1:0]   eop;
    rand logic [3-1:0]   empty;
    rand logic           vf_active;
    rand logic [10-1:0]  vf_num;
    rand logic [3-1:0]   bar_range;
    rand logic [1-1:0]   valid;

    ////////////////////////////
    // function
    function new ();
        this.vf_active = 0; // vf is disabled in default
    endfunction

    virtual function sv_common_pkg::Transaction copy(sv_common_pkg::Transaction to = null);
        transaction tr;
        if(to == null) begin
            tr = new;
        end else begin
            $cast(tr, to);
        end

        tr.data =     data;
        tr.hdr  =     hdr;
        tr.prefix =   prefix;
        tr.sop =      sop;
        tr.eop =      eop;
        tr.empty =    empty;
        tr.vf_active = vf_active;
        tr.vf_num    = vf_num;
        tr.bar_range = bar_range;
        tr.valid =    valid;

        return tr;
    endfunction

    virtual function void display(string prefix = "");
        if(prefix != "") begin
            $write("---------------------------------------------------------\n");
            $write("-- %s\n",prefix);
            $write("---------------------------------------------------------\n");
        end
        $write("%s\n", this.convert2string());
    endfunction

    virtual function bit compare(input sv_common_pkg::Transaction to, output string diff,input int kind = -1);
        bit result = 1'b1;
        transaction rhs;
        $cast(rhs, to);

        result &= (data      == rhs.data);
        result &= (hdr       == rhs.hdr);
        result &= (prefix    == rhs.prefix);
        result &= (sop       == rhs.sop);
        result &= (vf_active == rhs.vf_active);
        result &= (vf_num    == rhs.vf_num);
        result &= (eop       == rhs.eop);
        result &= (empty     == rhs.empty);
        result &= (bar_range == rhs.bar_range);
        result &= (valid     == rhs.valid);

        return result;
    endfunction


    function string convert2string();
      string s;
      $sformat(s, {
          "data      = 'h%0h\n",
          "hdr       = 'h%0h\n",
          "prefix    = 'h%0h\n",
          "sop       = '%d\n",
          "eop       = '%d\n",
          "empty     = '%d\n",
          "vf_active = '%b\n",
          "vf_num    = '%d\n",
          "bar_range = 'h%0h\n",
          "valid     = '%d\n"},
          data, hdr, prefix, sop, eop, empty, vf_active, vf_num, bar_range, valid);
      return s;
    endfunction
endclass

