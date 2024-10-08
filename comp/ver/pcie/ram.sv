/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

class ram #(ADDR_WIDTH, MPS, MRRS) extends sv_common_pkg::Driver;

    localparam PAGE_SIZE = 4096;

    sv_ndp_software_pkg::ram_base #(ADDR_WIDTH)  ram_modul;
    int verbosity = 0;
    sv_common_pkg::tTransMbx mbx_output;

    function new(string inst, sv_common_pkg::tTransMbx mbx_request, sv_ndp_software_pkg::ram_base #(ADDR_WIDTH) ram_modul);
        super.new(inst, mbx_request);
        this.ram_modul = ram_modul;
        this.mbx_output = new();
    endfunction

    function void verbosity_set(int unsigned level);
        verbosity = level;
    endfunction

    virtual task run();
        sv_common_pkg::Transaction tr_new;
        PcieRequest tr;

        while(enabled) begin
            byte unsigned data[];
            int unsigned length;
            logic [63:0] address;


            // get request
            transMbx.get(tr_new);
            $cast(tr, tr_new);

            // data and address is alligned to 4bytes
            if ((({tr.addr, 2'b00} & (PAGE_SIZE-1)) + tr.data.size()*4) > PAGE_SIZE) begin
                tr.display();
                $error("PCIE: transaction continuos throught page boundary\n\tstart address : %h\n\tend address   : %h\n",
                                                                     {tr.addr, 2'b00}, {tr.addr, 2'b00} + data.size()*4);
                $stop();
            end

            tr.data_get(address, length, data);
            //////////////////////////////////////
            // REQUEST TYPE WRITE
            if (tr.type_tr == PCIE_RQ_WRITE) begin
                if (verbosity) begin
                    data_display("WRITE", data, address, tr.tag);
                end

                if (data.size() > MPS) begin
                    $error("%s ERROR: MPS is %6d but WRITE data size is %6d\n", inst, MPS, data.size());
                    $finish();
                end

                ram_modul.write(address, data.size(), data);
            end

            //////////////////////////////////////
            // REQUEST TYPE READ
            if (tr.type_tr == PCIE_RQ_READ) begin
               byte unsigned data_read[];

               //check READ RQ
               if (length > MRRS) begin
                   $error("%s ERROR: MRRS is %6d but READ data size is %6d\n", inst, MPS, length);
                   $finish();
               end

               data_read = new[length];
               ram_modul.read(address, length, data_read);

               if (verbosity) begin
                  data_display("READ", data_read, address, tr.tag);
               end

               send_response(address, tr.tag, data_read, tr.requester_id);
            end
        end
    endtask

    function data_display(string dir, byte unsigned data[], logic [ADDR_WIDTH-1:0] addr, int unsigned tag);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t: ", $time);
            $write("PCIe %s %s : %6d B <= %x (tag %x)\n", inst, dir, data.size(), addr, tag);

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
    endfunction

    task send_response(logic [6:0] addr, int unsigned tag,  byte unsigned data[], logic [31:0] requester_id);
        PcieCompletion tr_compl;
        sv_common_pkg::Transaction to;
        int unsigned length = data.size();

        //create completion
        tr_compl = new();
        tr_compl.lower_address = addr;
        tr_compl.byte_count    = data.size();
        tr_compl.tag           = tag;
        tr_compl.completed     = 1;
        tr_compl.requester_id  = requester_id;

        //setup fbe
        case (addr & 13'b11)
            0 : begin  end
            1 : begin  length += 1; data = {8'h00, data}; end
            2 : begin  length += 2; data = {8'h00, 8'h00, data}; end
            3 : begin  length += 3; data = {8'h00, 8'h00, 8'h00, data}; end
        endcase

        ////setup lbe
        case (data.size() & 3)
            0 : begin  end
            1 : begin  length += 3; data = {data, 8'h00, 8'h00, 8'h00}; end
            2 : begin  length += 2; data = {data, 8'h00, 8'h00}; end
            3 : begin  length += 1; data = {data, 8'h00}; end
        endcase

        tr_compl.length = length/4;
        tr_compl.data = { << 32{ {<< 8 {data}} }};

        // put to transaction fifo
        $cast(to, tr_compl);
        mbx_output.put(to);

        if (verbosity > 3) begin
            to.display({inst, " READ TRANSACTION"});
        end
    endtask
endclass
