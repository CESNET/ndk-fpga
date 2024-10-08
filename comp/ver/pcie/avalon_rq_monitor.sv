/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

class avalon_rq_monitor extends sv_common_pkg::Monitor;
    ////////////////////////
    // Variable
    pcie_monitor_cbs    avalon_rq_cbs;
    int unsigned verbosity = 0;

    typedef enum {IDLE, READ} state_t;
    state_t state;
    logic [31:0] data[$];
    PcieRequest hl_tr;


     function new (string inst = "");
        super.new(inst);
        avalon_rq_cbs = new();
     endfunction

    function void verbosity_set(int unsigned level);
        verbosity = level;
    endfunction

    virtual task run();
        sv_common_pkg::Transaction common_tr;
        avst_rx::transaction tr;

        while(enabled) begin
            avalon_rq_cbs.get(common_tr);
            $cast(tr, common_tr);

            if (verbosity > 4) begin
                tr.display({inst, " RQ TRANSACTION"});
            end

            if(tr.sop == 1'b1) begin
                logic [128-1:0] hdr;
                data = {};
                hl_tr = new();
                hdr[128-1:96] = tr.hdr[32-1:0];
                hdr[96-1:64]  = tr.hdr[64-1:32];
                hdr[64-1:32]  = tr.hdr[96-1:64];
                hdr[32-1:0]   = tr.hdr[128-1:96];

                if(hdr[30:29] == 2'b11) begin
                    hl_tr.type_tr = PCIE_RQ_WRITE;
                    hl_tr.addr    = {hdr[95:64], hdr[127:98]};
                    state = READ;
                end

                if(hdr[30:29] == 2'b10) begin
                    hl_tr.type_tr = PCIE_RQ_WRITE;
                    hl_tr.addr    = hdr[95:66];
                    state = READ;
                end

                if(hdr[30:29] == 2'b01) begin
                    hl_tr.type_tr = PCIE_RQ_READ;
                    hl_tr.addr    = {hdr[95:64], hdr[127:98]};
                end

                if(hdr[30:29] == 2'b00) begin
                    hl_tr.type_tr = PCIE_RQ_READ;
                    hl_tr.addr    = hdr[95:66];
                end

                hl_tr.length = hdr[9:0];
                hl_tr.tag    = {hdr[23], hdr[19], hdr[47:40]};
                hl_tr.fbe    = hdr[35:32];
                hl_tr.lbe    = hdr[39:36];
                hl_tr.requester_id = hdr[63:48]; // Request ID. (63:56 = BUS NUM, 55:48 = VF ID)
            end

            if(state == READ) begin
                int m_end = 8;
                if (data.size() + m_end >= hl_tr.length) begin
                     m_end = hl_tr.length - data.size();
                end

                //read data from buss
                for (int i = 0; i < m_end; i++) begin
                    data.push_back(tr.data[(i+1)*32-1 -:32]);
                end
            end

            if(tr.eop == 1'b1) begin
                sv_common_pkg::Transaction to;

                if (hl_tr.length == 1) begin
                    hl_tr.lbe = hl_tr.fbe;
                end

                state = IDLE;
                hl_tr.data  = data;
                $cast(to, hl_tr);
                foreach(cbs[it]) begin
                    cbs[it].post_rx(to, inst);
                end

                if (verbosity > 4) begin
                     hl_tr.display({inst, " CREATE FRAME"});
                end
            end
        end
    endtask

endclass

