/* \scoreboard.sv
 * \brief Verification scoreboard
 * \author Daniel Kondys <xkondy00@vutbr.cz>
 * \date 2020
 */
/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import sv_common_pkg::*;
import sv_mi_pkg::*;

class GoldenModel #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH, PORTS, ADDR_MASK, ADDR_BASES, logic [ADDR_WIDTH-1:0] ADDR_BASE[ADDR_BASES], int PORT_MAPPING[ADDR_BASES]) extends MiTransaction #(DATA_WIDTH, ADDR_WIDTH);
    bit enable;
    //requests
    mailbox #(MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)) master_rq;
    mailbox #(MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)) slave_rq_tr[PORTS];
    //responses
    mailbox #(MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)) master_rs;
    mailbox #(MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)) slave_rs_tr[PORTS];

    function new();
        master_rq = new();
        for (int i = 0; i < PORTS; i++) begin
            slave_rq_tr[i] = new();
        end

        master_rs = new();
        for (int i = 0; i < PORTS; i++) begin
            slave_rs_tr[i] = new();
        end
    endfunction

    function int port_num (MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) tr);
        logic[ADDR_WIDTH-1:0] masked_addr;

        masked_addr = tr.address & ADDR_MASK;
        port_num = PORT_MAPPING[ADDR_BASES-1];
        for (int i = 0; i < ADDR_BASES-1; i++) begin
            if ((masked_addr >= (ADDR_BASE[i] & ADDR_MASK)) && (masked_addr < (ADDR_BASE[i+1] & ADDR_MASK))) begin
                port_num = PORT_MAPPING[i];
                break;
            end
        end
        return port_num;
    endfunction

    task setDisable();
        enable = 0;
    endtask

    task setEnable();
        enable = 1;
        fork
            testRQ();
            testRS();
        join_none
    endtask

    task testRQ();
        int i = 1;
        while (enable) begin
            MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) master_tr;
            MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) slave_tr;
            int pnum;
            bit empty;
            int j = 0;
            string dif;

            master_rq.get(master_tr);
            pnum = port_num(master_tr);
            while (j < 200) begin
                empty = slave_rq_tr[pnum].try_get(slave_tr);
                if (empty == 0) begin
                    #10ns;
                    j++;
                end else begin
                    break;
                end
            end
            if (empty == 0) begin
                $write("Mailbox still empty'\n");
                $stop();
            end else if (!master_tr.compare(slave_tr, dif)) begin
                $write("REQUESTS are not the same (%4d)\n", i);
                master_tr.display("master");
                slave_tr.display("slave");
                $stop();
            end
            i++;
        end
    endtask

    task testRS();
        int i = 1;
        while (enable) begin
            MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) master_tr;
            MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) slave_tr;
            int pnum;
            bit empty;
            string dif;

            master_rs.get(master_tr);
            pnum = port_num(master_tr);
            empty = slave_rs_tr[pnum].try_get(slave_tr);
            if (empty == 0) begin
                $write("The calculated mailbox (%4d) is empty (address is: %8x)\n", pnum, master_tr.address);
                $stop();
            end else if (!master_tr.compare(slave_tr, dif)) begin
                $write("RESPONSES are not the same (%4d)\n", i);
                master_tr.display("master");
                slave_tr.display("slave");
                $stop();
            end
            i++;
        end
    endtask
endclass

class slaveCbs #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH, PORTS, ADDR_MASK, ADDR_BASES, logic [ADDR_WIDTH-1:0] ADDR_BASE[ADDR_BASES], int PORT_MAPPING[ADDR_BASES]) extends MonitorCbs;
    GoldenModel #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH, PORTS, ADDR_MASK, ADDR_BASES, ADDR_BASE, PORT_MAPPING) gm;
    int port;

    function new(GoldenModel #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH, PORTS, ADDR_MASK, ADDR_BASES, ADDR_BASE, PORT_MAPPING) gm, int port);
        this.gm = gm;
        this.port = port;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) tr = new;

        transaction.copy(tr);
        if (tr.tr_type == TR_REQUEST) begin
			if (tr.op != OP_NONE) begin
            	gm.slave_rq_tr[port].put(tr);
			end
        end
        if (tr.tr_type == TR_RESPONSE) begin
            gm.slave_rs_tr[port].put(tr);
        end
    endtask
endclass

class masterCbs #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH, PORTS, ADDR_MASK, ADDR_BASES, logic [ADDR_WIDTH-1:0] ADDR_BASE[ADDR_BASES], int PORT_MAPPING[ADDR_BASES]) extends MonitorCbs;
    GoldenModel #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH, PORTS, ADDR_MASK, ADDR_BASES, ADDR_BASE, PORT_MAPPING) gm;
    int cnt = 0;

    function new(GoldenModel #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH, PORTS, ADDR_MASK, ADDR_BASES, ADDR_BASE, PORT_MAPPING) gm);
        this.gm = gm;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) tr = new;

        transaction.copy(tr);
        if (tr.tr_type == TR_REQUEST) begin
			if (tr.op != OP_NONE) begin
	            gm.master_rq.put(tr);
			end
        end
        if (tr.tr_type == TR_RESPONSE) begin
            gm.master_rs.put(tr);
        end
        cnt++;
        if (cnt % 100000 == 0) begin
            $write("%4d transactions have been sent/recieved\n", cnt);
        end
    endtask
endclass

class Scoreboard #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH, PORTS, ADDR_MASK, ADDR_BASES, logic [ADDR_WIDTH-1:0] ADDR_BASE[ADDR_BASES], int PORT_MAPPING[ADDR_BASES]);

    masterCbs   #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH, PORTS, ADDR_MASK, ADDR_BASES, ADDR_BASE, PORT_MAPPING) rxCbs;
    slaveCbs    #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH, PORTS, ADDR_MASK, ADDR_BASES, ADDR_BASE, PORT_MAPPING) txCbs[PORTS];
    GoldenModel #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH, PORTS, ADDR_MASK, ADDR_BASES, ADDR_BASE, PORT_MAPPING) gm;

    function new ();
        gm = new();
        rxCbs = new(gm);
        for (int i = 0; i < PORTS; i++) begin
            txCbs[i] = new(gm, i);
        end
    endfunction

    task setEnable();
        gm.setEnable();
    endtask

    task setDisable();
        gm.setDisable();
    endtask

endclass
