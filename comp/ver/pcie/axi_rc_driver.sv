/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

class axi_rc_driver extends sv_common_pkg::Driver;
    int unsigned verbosity = 0;

    ////////////////////
    // functions
    function new(string inst, sv_common_pkg::tTransMbx mbx);
        super.new(inst, mbx);
    endfunction

    task run();

        while(enabled == 1'b1) begin
            send_packet();
        end
    endtask

    function void verbosity_set(int unsigned level);
        verbosity = level;
    endfunction

    //send fram in one block
    task send_packet();
        sv_common_pkg::Transaction tr_send;
        sv_axi_pcie_pkg::AxiTransaction #(8) tr_axi;
        PcieCompletion tr;
        sv_common_pkg::Transaction tr_recv;
        //transform variable
        logic[95:0] header;
        byte unsigned headerArray[12];
        byte unsigned data[];
        logic[11:0] address = '0;
        bit completed;
        int lbe_length;
        logic [7:0]  tag;
        logic [10:0] length;
        logic [15:0]  requester_id;

        //get PCIE COMPLETION
        transMbx.get(tr_recv);
        $cast(tr, tr_recv);

        //create axi transaction
        tr_axi = new();

        //setup lbe
        lbe_length = tr.byte_count;
        case (tr.lower_address & 13'b11)
            0 : begin tr_axi.fbe = 4'b1111; lbe_length += 0; end
            1 : begin tr_axi.fbe = 4'b1110; lbe_length += 1; end
            2 : begin tr_axi.fbe = 4'b1100; lbe_length += 2; end
            3 : begin tr_axi.fbe = 4'b1000; lbe_length += 3; end
        endcase

        completed    = tr.completed; // it shoudl be counted
        tr_axi.lbe = 4'b1111;
        if(completed == 1'b1) begin
            ////setup lbe
            case (lbe_length & 3)
                0 : begin tr_axi.lbe = 4'b1111; end
                1 : begin tr_axi.lbe = 4'b0001; end
                2 : begin tr_axi.lbe = 4'b0011; end
                3 : begin tr_axi.lbe = 4'b0111; end
            endcase
        end

        if (tr.length == 1) begin
            tr_axi.fbe &= tr_axi.lbe;
            tr_axi.lbe = 0;
        end

        //////////////////////////////
        //CREATE AXI TRANSACTION
        tag          = tr.tag;
        address      = '0;
        address[6:0] = tr.lower_address;
        length       = tr.length;
        requester_id = tr.requester_id;
        header = {
            8'h00, requester_id, tag,
            16'h0, 5'b00000, length,
            1'b0, completed, 1'b0, length, 2'b00, 4'b0000, address
        };

        data = { << 32{ {<< 8 {tr.data}} }};
        {<<byte{headerArray}} = header;
        tr_axi.data = {headerArray, data};

        if (verbosity>1) begin
            tr_axi.display({inst, " SEND AXI TRANSACTION"});
        end

        //send transaction
        $cast(tr_send, tr_axi);
        foreach (cbs[i])
            cbs[i].pre_tx(tr_send, inst);
        /* No-op = virtual driver */
        foreach (cbs[i])
            cbs[i].post_tx(tr_send, inst);
    endtask
endclass

