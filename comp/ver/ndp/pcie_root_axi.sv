/*!
 * \file       pcie_root_axi.sv
 * \brief      PCIe root emulation unit for AXI transactions (Virtex7, US+)
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */


let min(a,b) = (a < b) ? a : b;
import sv_common_pkg::*;
import sv_axi_pkg::*;

class ReadRequest;
    logic[63:0] address;
    logic[12:0] length;
    logic[7:0] tag;

    int remains;
    time timeToNextSend;

    function new();
    endfunction
endclass

class PCIeRootAxi #(ADDR_WIDTH = 32, PAGE_SIZE = 4096) extends MonitorCbs;

    parameter CLK_PERIOD        = 10ns;
    const int REQ_TYPE_READ    = 0;
    const int REQ_TYPE_WRITE   = 1;

    const int RCB = 64;
    const int MPS = 256;

    bit enabled;

    int verbosity = 0;

    string inst_name;

    ReadRequest readRequests[$];
    semaphore readRequestsSema;

    ram_base #(ADDR_WIDTH) ram;

    tTransMbx transMbx;

    function new (ram_base #(ADDR_WIDTH) ram, string name = "");
        this.ram = ram;
        this.inst_name = name;
        readRequestsSema = new(1);
        transMbx = new();
    endfunction

    virtual task setEnabled();
        enabled = 1;
        fork
            run();
        join_none;
    endtask

    virtual task setDisabled();
        enabled = 0;
    endtask

    virtual task post_rx(Transaction transaction, string inst);
        AxiTransaction tr;

        logic[127:0] header;

        logic[63:0] address;
        logic[12:0] length;
        logic[3:0] request;
        logic[7:0] tag;

        logic [3:0] fbe;
        logic [3:0] lbe;

        byte unsigned buffer[$];
        int unsigned  addr_move = 0;
        string time_act;
        $cast(tr, transaction);

        header      = {<<8{tr.data[0:15]}};

        address     = {header[63:2], 2'b00};
        length      = {header[74:64], 2'b00};
        request     = header[78:75];
        tag         = header[103:96];

        fbe         = tr.fbe;
        lbe         = (length == 4) ? tr.fbe : tr.lbe;

        if (verbosity)
            tr.display("PCIE: root complex input transaction");

        //check if data is not continue throught page boundary
        if (((address & (PAGE_SIZE-1)) + length) > PAGE_SIZE) begin
             tr.display();
             $error("PCIE: transaction continuos throught page boundary\n\tstart address : %h\n\tend address   : %h\n", address, address+length);
             $stop();
        end

        ////correct address by fbe
        if (fbe[0] == 1'b1 || (length == 4 && fbe[3:0] == 4'b0000)) begin
             addr_move = 0;
        end else if (fbe[1:0] == 2'b10) begin
             addr_move = 1;
             length   -= 1;
        end else if (fbe[2:0] == 3'b100) begin
             addr_move = 2;
             length   -= 2;
        end else if (fbe[3:0] == 4'b1000) begin
             addr_move = 3;
             length   -= 3;
        end else begin
            $error("AXI PCIe - wrong fbe %h transaction size %d\n", fbe, length);
        end

        //corect length transaction by lbe
        if (lbe[3] == 1'b1 || (length == 4 && lbe[3:0] == 4'b0000)) begin
             ; //do nothing
        end else if (lbe[3:2] == 2'b01) begin
             length  -= 1;
        end else if (lbe[3:1] == 3'b001) begin
             length  -= 2;
        end else if (lbe[3:0] == 4'b0001) begin
             length  -= 3;
        end else begin
            $error("AXI PCIe - wrong lbe %h transaction size %d\n", lbe, length);
        end

        if (request == REQ_TYPE_WRITE) begin
            //buffer.delete();
            for (int unsigned it  = 0; it < length; it++) begin
                buffer.push_back(tr.data[16+addr_move+it]);
            end

            handleWriteTransaction(address + addr_move, buffer);
        end else if (request == REQ_TYPE_READ) begin
            if (tr.data.size != 16) begin
                $timeformat(-9, 3, " ns", 8);
                $write("Time: %t: ", $time);
                $error("AXI - PCIe %s read transaction length mismatch!\n", inst_name);
            end
            handleReadRequest(address + addr_move, length, tag);
        end
    endtask

    task handleWriteTransaction(logic[63:0] address, byte unsigned data[]);
        ram.write(address, data.size(), data);

        if (verbosity) begin
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t: ", $time);
            $write("PCIe %s write: %x B => %x", inst_name, data.size(), address);

            if (data.size()==0) begin
                $error("PCIe %s: Zero length request!\n", inst_name);
                $stop;
            end

            if (verbosity > 1) begin
                for (integer j = 0; j < data.size(); j++) begin
                    if (j % 32 == 0)
                        $write("\n%4x:", j);
                    if (j % 8 == 0)
                        $write(" ");
                    $write("%x ", data[j]);
                end
            end
            $write("\n");
        end
    endtask

    task handleReadRequest(logic[63:0] address, logic[12:0] length, logic[7:0] tag);
        int i;
        byte unsigned data [];

        ReadRequest rr = new();
        rr.address = address;
        rr.length = length;
        rr.tag = tag;
        rr.remains = length;
        rr.timeToNextSend = $time + $urandom_range(40, 10)*CLK_PERIOD;

        readRequestsSema.get();
        i = 0;
        while (i < readRequests.size()) begin
            if (rr.timeToNextSend < readRequests[i].timeToNextSend)
                break;
            i++;
        end
        readRequests.insert(i, rr);
        readRequestsSema.put();

        if (verbosity) begin
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t: ", $time);
            $write("PCIe %s read : %x B <= %x (tag %x)\n", inst_name, length, address, tag);

            if (length==0) begin
                $error("PCIe %s: Zero length request!\n", inst_name);
                $stop;
            end

            if (verbosity > 1) begin
                data = new[length];
                ram.read(rr.address, length, data);

                for (integer j = 0; j < length; j++) begin
                    if (j % 32 == 0)
                        $write("\n%4x:", j);
                    if (j % 8 == 0)
                        $write(" ");
                    $write("%x ", data[j]);
                end
            end
            $write("\n");
        end
    endtask

    task run();
        int i;
        ReadRequest rr;

        while (enabled) begin
            readRequestsSema.get();
            if (readRequests.size() && readRequests[0].timeToNextSend <= $time) begin
                rr = readRequests[0];
                readRequests.delete(0);
                readRequestsSema.put();

                handleReadRequestPart(rr);

                if (rr.length) begin
                    rr.timeToNextSend = $time + $urandom_range(10, 0)*CLK_PERIOD;
                    readRequestsSema.get();
                    i = 0;
                    while (i < readRequests.size()) begin
                        if (rr.timeToNextSend < readRequests[i].timeToNextSend)
                            break;
                        i++;
                    end
                    readRequests.insert(i, rr);
                    readRequestsSema.put();
                end
            end else begin
                readRequestsSema.put();
                #(CLK_PERIOD);
            end
        end
    endtask

    task handleReadRequestPart(ReadRequest rr);
        AxiTransaction tr;
        Transaction to;
        int lengthRem;
        int length;
        int rcbs, rcbs_max;
        byte unsigned data [];

        /* Generate number of RCB blocks for this completion (between 1 and all remaining RCB for read request) */
        rcbs_max = (rr.length + (rr.address & (RCB-1)) + RCB-1) / RCB;
        rcbs = $urandom_range(rcbs_max, 1);

        /* Compute allowed length of current transaction */
        length = 0;
        lengthRem = rr.length;
        for (int i = 0; i < rcbs; i++) begin
            if (length == 0 && rr.address & (RCB-1)) begin
                /* Align to RCB */
                length = min(RCB - (rr.address & (RCB-1)), rr.length);
                lengthRem -= length;
            end else if (lengthRem >= RCB) begin
                if (length + RCB > MPS)
                    break;
                length += RCB;
                lengthRem -= RCB;
            end else begin
                if (length + lengthRem > MPS)
                    break;
                length += lengthRem;
                lengthRem = 0;
            end
        end

        tr = new();
        data = new[length];
        ram.read(rr.address, length, data);


        rr.length -= length;
        prepareCompletion(rr.address, data, rr.tag, rr.length == 0 ? 1 : 0, tr);
        rr.address += length;

        if (verbosity) begin
            $write("%t PCIe %s completion Tag %02x: Address %07x, Remaining length %03x, Remaining RCBs: %d, Current RCBs: %d, Length: %03x | %s\n", $time, inst_name, rr.tag, rr.address-length, rr.length+length, rcbs_max, rcbs, length, rr.length == 0 ? "Completed" : "Unfinished" );

            if (verbosity > 1) begin
                for (integer j = 0; j < length; j++) begin
                    if (j % 32 == 0)
                        $write("\n%4x:", j);
                    if (j % 8 == 0)
                        $write(" ");
                    $write("%x ", data[j]);
                end
            end
            $write("\n");
        end

        $cast(to, tr);
        transMbx.put(to);
    endtask

    task prepareCompletion(logic[11:0] address, byte unsigned data[], logic[7:0] tag, bit completed, AxiTransaction tr);
        logic[95:0] header;
        byte unsigned headerArray[12];
        logic [12:0]  length;


        //setup lbe
        case (address & 13'b11)
            0 : begin tr.fbe = 4'b1111; end
            1 : begin tr.fbe = 4'b1110; address -= 1; data = {8'h00, data}; end
            2 : begin tr.fbe = 4'b1100; address -= 2; data = {8'h00, 8'h00, data}; end
            3 : begin tr.fbe = 4'b1000; address -= 3; data = {8'h00, 8'h00, 8'h00, data}; end
        endcase


        ////setup lbe
        case (data.size() & 3)
            0 : begin tr.lbe = 4'b1111; end
            1 : begin tr.lbe = 4'b0001; data = {data, 8'h00, 8'h00, 8'h00}; end
            2 : begin tr.lbe = 4'b0011; data = {data, 8'h00, 8'h00}; end
            3 : begin tr.lbe = 4'b0111; data = {data, 8'h00}; end
        endcase

        if (data.size() == 4) begin
            tr.fbe &= tr.lbe;
            tr.lbe = 0;
        end

        length = data.size();
        header = {
            24'h000000, tag,
            16'h0, 5'b00000, length[12:2],
            1'b0, completed, 1'b0, length, 4'b0000, address
        };

//        if (verbosity)
//            $write("%t PCIe %s completion: %x B <= %x (tag %x), completed: %d\n", $time, inst_name, length, address, tag, completed);

        {<<byte{headerArray}} = header;
        tr.data = {headerArray, data};
    endtask

endclass

