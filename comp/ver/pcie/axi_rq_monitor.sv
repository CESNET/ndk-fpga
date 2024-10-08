/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/


class axi_rq_monitor extends sv_common_pkg::Monitor;
    pcie_monitor_cbs    axi_rq_cbs;

    PcieRequest hl_tr;
    int unsigned verbosity = 0;

    function new (string inst = "");
        super.new(inst);
        axi_rq_cbs = new();
     endfunction

    function void verbosity_set(int unsigned level);
        verbosity = level;
    endfunction

    virtual task run();
        while(enabled) begin
            sv_common_pkg::Transaction common_tr;
            sv_axi_pcie_pkg::AxiTransaction #(8) tr;
            logic[127:0] header;
            int unsigned data_length;

            //get transaction and header
            axi_rq_cbs.get(common_tr);
            $cast(tr, common_tr);
            header = {<<8{tr.data[0:15]}};

            //create PCIE TRANSACTION
            hl_tr        = new();
            hl_tr.length = header[74:64]; //length is in DWORDS
            if (header[78:75] == 0) begin
                hl_tr.type_tr = PCIE_RQ_READ;
                hl_tr.data = {};
            end else if (header[78:75] == 1) begin
                logic [31:0] data_test[];
                hl_tr.type_tr = PCIE_RQ_WRITE;

                //resize becouse strange behavioral of axi agent
                hl_tr.data   = new[hl_tr.length];
                for (int unsigned it = 0; it < hl_tr.length; it++) begin
                    hl_tr.data[it][8-1:0]   = tr.data[16 + it*4 + 0];
                    hl_tr.data[it][16-1:8]  = tr.data[16 + it*4 + 1];
                    hl_tr.data[it][24-1:16] = tr.data[16 + it*4 + 2];
                    hl_tr.data[it][32-1:24] = tr.data[16 + it*4 + 3];
                end
            end else begin
                $error ("%s Unknown type of transaction %h\n", inst, header[78:75]);
                $finish();
            end
            hl_tr.tag    = header[103:96];
            hl_tr.addr   = header[63:2];
            hl_tr.fbe    = tr.fbe;
            hl_tr.lbe    = (hl_tr.length == 1) ? tr.fbe : tr.lbe;
            hl_tr.requester_id = header[95:80];

            if(verbosity>1) begin
                hl_tr.display({inst, " Create PCIE RQ"});
            end

            foreach(cbs[it]) begin
                cbs[it].post_rx(hl_tr, inst);
            end
        end
    endtask
endclass
