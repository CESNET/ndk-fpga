/*
 * transaction.sv pcie competition transaction
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

typedef enum {PCIE_RQ_READ, PCIE_RQ_WRITE} pcie_rq_type_t;

class Transaction extends sv_common_pkg::Transaction;
    int unsigned data_size_max = 256;
    int unsigned data_size_min = 1;

    rand int  unsigned data_size;
    rand logic [64-1:0] addr;
    rand bit rw;

    constraint c1 {
        data_size   <= data_size_max;
        data_size   >= data_size_min;
        ((addr % 4096) + data_size)  <= 4096;
    }

    ///////////////////////////////////////
    // display function
    virtual function void display(string prefix = "");
        string tr_type;
        if (prefix != "") begin
            $write("---------------------------------------------------------\n");
            $write("-- %s\n",prefix);
            $write("---------------------------------------------------------\n");
        end

        if(rw == 1) begin
            tr_type = "WRITE";
        end else begin
            tr_type = "READ";
        end

        $write("Type : %s\nAddr : %h\nData size : %6d\n", tr_type, addr, data_size);
    endfunction

   ///////////////////////////////////////
   // copy function
   virtual function sv_common_pkg::Transaction copy(sv_common_pkg::Transaction to = null);
        Transaction tr;
        sv_common_pkg::Transaction ret;

        if (to == null) begin
            tr = new();
        end else begin
            $cast(tr, to);
        end

        tr.data_size = data_size;
        tr.addr      = addr;
        tr.rw        = rw;

        $cast(ret, tr);
        return ret;
    endfunction
endclass

class PcieCompletion extends sv_common_pkg::Transaction;
    int unsigned tag;
    logic [9:0]  dword_count;
    logic [6:0]  lower_address;
    logic [11:0] byte_count;
    logic [31:0] data[];

    virtual function void display(string prefix = "");
        if(prefix != "") begin
            $write("---------------------------------------------------------\n");
            $write("-- %s\n",prefix);
            $write("---------------------------------------------------------\n");
        end
        $write("%s\n", this.convert2string());
    endfunction

    virtual function sv_common_pkg::Transaction copy(sv_common_pkg::Transaction to = null);
        PcieCompletion rhs;

        if(to == null) begin
            rhs = new();
        end else begin
            $cast(rhs, to);
        end

        rhs.tag  = tag;
        rhs.dword_count = dword_count;
        rhs.lower_address = lower_address;
        rhs.byte_count = byte_count;
        rhs.data = data;
        return rhs;
    endfunction

    function string convert2string();
        string num_to_str;
        string s = "";

        $sformat(num_to_str, "PcieCompletion\n\tlower addr %h\n\tdword_count %d\n\ttag %h\n\tbyte_count %d\n", lower_address, dword_count, tag, byte_count);
        s = {s, num_to_str};

        for (int unsigned i = 0; i < data.size; i++) begin
            $sformat(num_to_str, "%8h", data[i]);
            if (i % 8 == 0) begin
                s = {s, "\n\t", num_to_str};
            end else begin
                s = {s,"  ", num_to_str};
            end
        end
        s ={s, "\n\n"};

        return s;
    endfunction
endclass



class PcieRequest extends sv_common_pkg::Transaction;

    pcie_rq_type_t type_tr;
    int unsigned  tag;
    logic [63:2] addr;
    logic [3:0]  fbe;
    logic [3:0]  lbe;
    logic [9:0]  length; //length in DWORDS
    logic [31:0] data[];


    ///////////////////////////////////
    // copy, compare, convert to string function
    function new ();
    endfunction

    virtual function sv_common_pkg::Transaction copy(sv_common_pkg::Transaction to = null);
        PcieRequest rhs;

        if(to == null) begin
            rhs = new();
        end else begin
            $cast(rhs, to);
        end

        rhs.type_tr = type_tr;
        rhs.data = data;
        rhs.addr = addr;
        rhs.length = length;
        rhs.tag  = tag;
        rhs.fbe  = fbe;
        rhs.lbe  = lbe;
        return rhs;
    endfunction


    virtual function bit compare(input sv_common_pkg::Transaction to, output string diff, input int kind = -1);
        bit result = 1'b1;
        PcieRequest tr;
        $cast(tr, to);

        result &= (type_tr === tr.type_tr);
        result &= (fbe === tr.fbe);
        result &= (addr === tr.addr);
        result &= (length === tr.length);
        result &= (tag === tr.tag);
        result &= (lbe === tr.lbe);
        result &= (fbe === tr.fbe);
        result &= (data.size() === tr.data.size());
        if (result == 0) begin
            return 0;
        end

        for (int unsigned i = 0; i < data.size; i++) begin
            if (data[i] != tr.data[i]) begin
                return 0;
            end
        end

        return 1;
    endfunction

    virtual function void display(string prefix = "");
        if(prefix != "") begin
            $write("---------------------------------------------------------\n");
            $write("-- %s\n",prefix);
            $write("---------------------------------------------------------\n");
        end
        $write("%s\n", this.convert2string());
    endfunction

    function string convert2string();
        string num_to_str;
        string s = "";

        $sformat(num_to_str, "PcieRequest\n\tTransaction type : %s\n\taddr %h\n\tlength %d\n\ttag %h\n\tfbe : %h \tlbe : %h\n", type_tr, {addr, 2'b00}, length*4, tag, fbe, lbe);
        s = {s, num_to_str};

        for (int unsigned i = 0; i < data.size; i++) begin
            $sformat(num_to_str, "%8h", data[i]);
            if (i % 8 == 0) begin
                s = {s, "\n\t", num_to_str};
            end else begin
                s = {s,"  ", num_to_str};
            end
        end
        s ={s, "\n\n"};

        return s;
    endfunction
endclass
