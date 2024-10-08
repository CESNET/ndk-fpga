/* pcie_transaction.sv
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Martin Spinler <spinler@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */


class PcieCompletion extends sv_common_pkg::Transaction;
    int unsigned tag;
    logic [15:0] requester_id;
    bit [9:0] length;
    bit [6:0] lower_address;
    bit [11:0] byte_count;
    bit completed;
    bit [31:0] data[];

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
        rhs.length = length;
        rhs.lower_address = lower_address;
        rhs.byte_count = byte_count;
        rhs.completed  = completed;
        rhs.data = data;
        rhs.requester_id = requester_id;

        return rhs;
    endfunction

    function string convert2string();
        string num_to_str;
        string s = "";

        $sformat(num_to_str, "PcieCompletion\n\tlower addr %h\n\tlength %d\n\ttag %h\n\tbyte_count %d\n\tCompleted %b\n", lower_address, length, tag, byte_count, completed);
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
    logic [15:0] requester_id;
    int unsigned  tag;
    logic [63:2] addr;
    logic [9:0]  length; //length in DWORDS
    logic [3:0]  fbe;
    logic [3:0]  lbe;
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
        rhs.requester_id = requester_id;

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
        result &= (requester_id == tr.requester_id);
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

    function void data_get(output logic [63:0] out_addr, output int unsigned out_length, output byte unsigned out_data[]);
           byte unsigned data_que[$];
           int unsigned  data_length;
           logic [63:0]  address;

           //deserialize data
           if (data.size() > 0) begin
                data_que = { << 32{ {<< 8 {data}} }};
            end

            //get not alligned address
            address = {addr, 2'b00};
            // correct addres acording to fbe
            data_length = {this.length, 2'b00};
            if (this.fbe[0] == 1'b1 || (data_length == 4 && this.fbe[3:0] == 4'b0000)) begin
                 address += 0;
            end else if (this.fbe[1:0] == 2'b10) begin
                 address += 1;
                 data_length  -= 1;
                 data_que.pop_front();
            end else if (this.fbe[2:0] == 3'b100) begin
                 address += 2;
                 data_length  -= 2;
                 data_que.pop_front();
                 data_que.pop_front();
            end else if (this.fbe[3:0] == 4'b1000) begin
                 address += 3;
                 data_length  -= 3;
                 data_que.pop_front();
                 data_que.pop_front();
                 data_que.pop_front();
            end else begin
                $error("PCIE - wrong fbe %h transaction size %d\n", this.fbe, data_length);
                $finish();
            end

            // corect length transaction by lbe
            if (this.lbe[3] == 1'b1 || (data_length == 4 && this.lbe[3:0] == 4'b0000)) begin
                 ; //do nothing
            end else if (this.lbe[3:2] == 2'b01) begin
                 data_length  -= 1;
                 data_que.pop_back();
            end else if (this.lbe[3:1] == 3'b001) begin
                 data_length  -= 2;
                 data_que.pop_back();
                 data_que.pop_back();
            end else if (this.lbe[3:0] == 4'b0001) begin
                 data_length  -= 3;
                 data_que.pop_back();
                 data_que.pop_back();
                 data_que.pop_back();
            end else begin
                $error("PCIE - wrong lbe %h transaction size %d\n", this.lbe, data_length);
                $finish();
            end

            out_addr   = address;
            out_length = data_length;
            out_data   = data_que;
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

