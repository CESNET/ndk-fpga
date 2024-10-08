/*
 * data.sv model for mtc
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

//check pcie response data
class response_data #(MI_WIDTH);
    int          byte_count;
    logic [63:0] addr;
    pcie2mi::PcieRequest rq;

    function new (pcie2mi::PcieRequest rq);
        logic [4-1:0] lbe;
        int dword_count = rq.length;
        $cast(this.rq, rq.copy());

        //fbe
        if      (1'b1    == rq.fbe[0:0]) begin this.addr = {rq.addr, 2'b00}; byte_count = dword_count*4 - 0; end
        else if (2'b10   == rq.fbe[1:0]) begin this.addr = {rq.addr, 2'b01}; byte_count = dword_count*4 - 1; end
        else if (3'b100  == rq.fbe[2:0]) begin this.addr = {rq.addr, 2'b10}; byte_count = dword_count*4 - 2; end
        else if (4'b1000 == rq.fbe[3:0]) begin this.addr = {rq.addr, 2'b11}; byte_count = dword_count*4 - 3; end
        else begin $error("UNSUPORTED FBE %b\n", rq.fbe); $stop(); end

        //lbe
        lbe=rq.lbe;
        if (0 == rq.lbe) begin
            if (rq.length == 1) begin
                lbe = rq.fbe;
            end else begin
                $error("UNSUPORTED LBE %b\n", lbe); $stop();
            end
        end
        if      (1'b1    == lbe[3:3]) begin  byte_count = byte_count - 0; end
        else if (2'b01   == lbe[3:2]) begin  byte_count = byte_count - 1; end
        else if (3'b001  == lbe[3:1]) begin  byte_count = byte_count - 2; end
        else if (4'b0001 == lbe[3:0]) begin  byte_count = byte_count - 3; end
        else begin $error("UNSUPORTED LBE %b\n", lbe); $stop(); end

    endfunction

    function int check(pcie2mi::PcieCompletion pcie_resp, ref sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH) mi_resp[$]);
        sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH) mi_tr;
        int unsigned it = 0;
        int unsigned data_size;
        logic [31:0] data [$];

        if (pcie_resp.lower_address != addr[6:0]) begin
            pcie_resp.display("UNEXPECTED ADDR");
            $error("WRONG address Expected addr %h\n", addr[6:0]);
            $stop();
        end

        if (pcie_resp.byte_count != byte_count) begin
            pcie_resp.display("UNEXPECTED BYTE COUNT");
            $error("expecting byte count %d\n", byte_count);
            $stop();
        end


        ////////////////////////////////////
        // GENERATE ARRAY FROM MI READ SEQUENCE
        data_size = pcie_resp.dword_count*4;
        // START LOOP PEALING
        mi_tr = mi_resp.pop_front();
        case (pcie_resp.lower_address[1:0] & 2'b11)
            0 : begin data_size -= 0; pcie_resp.data[0] &= 32'hffffffff; data.push_back(mi_tr.data & 32'hffffffff); end
            1 : begin data_size -= 1; pcie_resp.data[0] &= 32'hffffff00; data.push_back(mi_tr.data & 32'hffffff00); end
            2 : begin data_size -= 2; pcie_resp.data[0] &= 32'hffff0000; data.push_back(mi_tr.data & 32'hffff0000); end
            3 : begin data_size -= 3; pcie_resp.data[0] &= 32'hff000000; data.push_back(mi_tr.data & 32'hff000000); end
        endcase
        //MAIN LOOP
        for(int unsigned it = 1; it < pcie_resp.data.size(); it++) begin
            mi_tr = mi_resp.pop_front();
            data.push_back(mi_tr.data);
        end
        //END LOOP PEALING
        if (pcie_resp.byte_count < data_size) begin
            case ((pcie_resp.lower_address[1:0] + pcie_resp.byte_count) & 3)
                1 : begin data_size -= 3; pcie_resp.data[pcie_resp.data.size()-1] &= 32'h000000ff; data[data.size()-1] &= 32'h000000ff; end
                2 : begin data_size -= 2; pcie_resp.data[pcie_resp.data.size()-1] &= 32'h0000ffff; data[data.size()-1] &= 32'h0000ffff; end
                3 : begin data_size -= 1; pcie_resp.data[pcie_resp.data.size()-1] &= 32'h00ffffff; data[data.size()-1] &= 32'h00ffffff; end
                0 : begin data_size -= 0; pcie_resp.data[pcie_resp.data.size()-1] &= 32'hffffffff; data[data.size()-1] &= 32'hffffffff; end
            endcase
        end

        this.byte_count -= data_size;
        this.addr       += data_size;

        assert(data.size() == pcie_resp.data.size());
        for (int unsigned it = 0; it < data.size(); it++) begin
            if (data[it] !== pcie_resp.data[it]) begin
                $write("=====================================\n");
                $writeh("DATA FROM MI\n %p\n", data);
                $write("=====================================\n");
                pcie_resp.display("ERROR :  GET FROM PCIE");
                $error("GET WRONG DATA FROM PCIE\n");
                $stop();
            end
        end

        //pcie_resp.display("TEST CHECK NOT IMPLEMENTED!!!");
        return (byte_count == 0); // if byte_count is 0 then it was last completition in transaction
    endfunction


    function void display(string prefix = "");
        this.rq.display(prefix);
    endfunction
endclass

///////////////////////////////////////////////
// scoreboard data. Callbacks call function of this class
///////////////////////////////////////////////
class scoreboard_data #(MI_WIDTH);

    int unsigned verbose;
    //expected mi transaction
    sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH) expected[$];
    //read request data
    sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH) responded[$];

    response_data #(MI_WIDTH) pcie_data[int]; //tag is used as index

    ///////////////////////////////////
    // stats
    int unsigned pcie_read_transactions;
    int unsigned pcie_read_completions;
    int unsigned pcie_write_transactions;
    int unsigned mi_transaction_gen;
    int unsigned mi_transaction_compare;

    function new ();
        this.verbose = 0;
        this.pcie_read_transactions  = 0;
        this.pcie_read_completions   = 0;
        this.pcie_write_transactions = 0;
        this.mi_transaction_gen     = 0;
        this.mi_transaction_compare = 0;
    endfunction

    function void verbose_set(int unsigned level);
        this.verbose = level;
    endfunction

    function void mi_request_gen(logic [MI_WIDTH-1:0] addr, int unsigned bar_aperature,
                                int unsigned bar, sv_mi_pkg::op_type_t tr_type, logic [MI_WIDTH-1:0] data, logic [MI_WIDTH/8-1:0] be);
            sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH) mi;

            mi = new();
            mi.address = (addr & (2**bar_aperature-4)) + 0;
            mi.tr_type = sv_mi_pkg::TR_REQUEST;
            mi.op      = tr_type;
            mi.be      = be;
            mi.data    = data;

            expected.push_back(mi);
            mi_transaction_gen += 1;
    endfunction

    function void read(pcie2mi::PcieRequest tr);

        for (int unsigned it = 0; it < tr.length; it++) begin
            logic [3:0] be;

            be = '1;
            if (it == 0) begin
                be &= tr.fbe;
            end else if (it == tr.length -1) begin
                be &= tr.lbe;
            end
            mi_request_gen({tr.addr + it, 2'b00}, 24, 0, sv_mi_pkg::OP_READ, '0, be);
        end

        //register tag
        if (pcie_data.exists(tr.tag)) begin
            $error("VERIFICATION ERROR : GENERATED TAG %4d ALLREADY EXISTS AND HAVENT BEEN COMPLETED\n", tr.tag);
            $stop();
        end
        pcie_data[tr.tag] = new(tr);
    endfunction

    function void write(pcie2mi::PcieRequest tr);
        for (int unsigned it = 0; it < tr.data.size(); it++) begin
            logic [3:0] be;

            be = '1;
            if (it == 0) begin
                be &= tr.fbe;
            end else if (it == tr.data.size()-1) begin
                be &= tr.lbe;
            end
            mi_request_gen({tr.addr + it, 2'b00}, 24, 0, sv_mi_pkg::OP_WRITE, tr.data[it], be);
        end
   endfunction

    //request for pcie interface
    function void pcie_request(sv_common_pkg::Transaction tr);
         pcie2mi::PcieRequest tr_cpy;
        $cast(tr_cpy, tr.copy());

        if (tr_cpy.type_tr == pcie2mi::PCIE_RQ_WRITE) begin
            write(tr_cpy);
            pcie_write_transactions += 1;
        end else begin
            read(tr_cpy);
            pcie_read_transactions += 1;
        end
    endfunction

    //response on mi interface
    function void mi_proc(sv_common_pkg::Transaction transaction);
        sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH) tr;
        $cast(tr, transaction.copy());

        if (verbose > 0) begin
            tr.display("MI TRANSACTION");
        end

        if (tr.tr_type == sv_mi_pkg::TR_REQUEST) begin
            sv_mi_pkg::MiTransaction #(MI_WIDTH, MI_WIDTH) mi;
            string diff;

            if (expected.size() == 0) begin
                tr.display("UNEXPECTED TRANSACTION");
                $error("UNEXPECTED TRANSACTION");
                $stop();
            end
            mi = expected.pop_front();

            //compare mi transaction
            if (mi.compare(tr, diff) == 0) begin
                mi.display("MI WRITE EXPECTED");
                tr.display("MI WRITE GET");
                $error("COMPARE ERROR");
                $stop();
            end
            mi_transaction_compare += 1;
        end else begin
            responded.push_back(tr);
        end
    endfunction

    //s tagem uložit i zbytek..
    function void pcie_response(sv_common_pkg::Transaction tr);
        pcie2mi::PcieCompletion resp;

        $cast(resp, tr);
        if (verbose > 1) begin
            tr.display(" PCIE RESPONSE");
        end

        if (pcie_data.exists(resp.tag) == 0) begin
            tr.display("UNEXPECTED TAG");
            $error("CANNOT FIND ANY REQUEST WITH THIS TAG %4d\n", resp.tag);
            $stop();
        end

        if (pcie_data[resp.tag].check(resp, responded)) begin
            pcie_data.delete(resp.tag);
            pcie_read_completions += 1;
        end
    endfunction

    function void display(string prefix = "");
        if (prefix != "") begin
            $write("---------------------------------------------------------\n");
            $write("-- %s\n",prefix);
            $write("---------------------------------------------------------\n");
        end

        $write("read requests %d\n",    pcie_read_transactions);
        $write("read completions %d\n", pcie_read_completions);
        $write("write requests %d\n",   pcie_write_transactions);
        $write("MI request  %d/%d\n",   mi_transaction_compare, mi_transaction_gen);


        if (expected.size() != 0) begin
            $write("\n\n================================================================\n");
            $write("SOME DATA REMAIN IN DUT\n");
            $write("EXPECTED %d MI REQUESTS\n", expected.size());
            for (int unsigned it = 0; it < expected.size(); it++) begin
                expected[it].display("MI REQUESTS");
            end
        end

        if (pcie_data.num() != 0) begin
            int unsigned tmp_index;
            $write("\n\n================================================================\n");
            $write("SOME DATA REMAIN IN DUT\n");
            $write("DUT HAVEN'T RESPONSE ON %d PCIE REQUESTS\n", pcie_data.num());
            pcie_data.first(tmp_index);
            do
                pcie_data[tmp_index].display("PCIE READ REQUEST");
            while(pcie_data.next(tmp_index));
        end
    endfunction

    task wait_done();
        wait (expected.size() == 0);
        wait (pcie_data.num() == 0);
    endtask
endclass

