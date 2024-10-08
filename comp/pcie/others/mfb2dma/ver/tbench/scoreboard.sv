/* \scoreboard.sv
 * \brief Verification scoreboard
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import sv_common_pkg::*;
import sv_dma_pkg::*;
import test_pkg::*;

class ScoreboardGeneratorCbs;
    TransactionTable #(1) sc_table;

    function new (TransactionTable #(1) st);
        sc_table = st;
    endfunction

    virtual task post_gen(Transaction transaction);
        sc_table.add(transaction);
        if (FULL_PRINT == TRUE) begin
           $write("\nDMA transaction added to ScoreTable.\n");
           print_dma_trans(transaction);
           //transaction.display();
        end
    endtask

    virtual task print_dma_trans(ref Transaction transaction);
        DMABusCompletionTransaction dma_tr;
        bit [DMA_DOWNHDR_WIDTH-1 : 0] dma_header;
        $cast(dma_tr,transaction);
        {<<{dma_header}} = dma_tr.header;

        $write("SIZE: %d\n", dma_tr.size);
        $write("HDR: 0x%x\n", dma_header);
        $write("DATA (0x%x dwords):",(dma_tr.data.size/4));
        for (integer j=0; j < dma_tr.data.size; j++)
        begin
            if (j%32==0) $write("\n%4x:",j);
            if (j%8==0) $write(" ");
            $write("%x ",dma_tr.data[j]);
        end
        $write("\n");
    endtask
endclass

class ScoreboardDriverCbs extends DriverCbs;
    function new ();
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        if (FULL_PRINT == TRUE) begin
           $write("\nRX transaction send from monitor %s\n", inst);
           $timeformat(-9, 3, " ns", 8);
           $write("Time: %t\n", $time);
           transaction.display();
        end
    endtask
endclass

class ScoreboardMonitorCbs extends MonitorCbs;
    TransactionTable #(1) sc_table;

    function new (TransactionTable #(1) st);
        sc_table = st;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        bit status=0;
        sc_table.remove(transaction, status);
        if (status==0)begin
            $write("\nUnknown transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            print_dma_trans(transaction);
            //transaction.display();
            sc_table.display();
            $stop;
        end;
        if (FULL_PRINT == TRUE) begin
           $write("\nDMA transaction received from monitor %s\n", inst);
           $timeformat(-9, 3, " ns", 8);
           $write("Time: %t\n", $time);
           print_dma_trans(transaction);
        end
    endtask

    virtual task print_dma_trans(ref Transaction transaction);
        DMABusCompletionTransaction dma_tr;
        bit [DMA_DOWNHDR_WIDTH-1 : 0] dma_header;
        $cast(dma_tr,transaction);
        {<<{dma_header}} = dma_tr.header;

        $write("SIZE: %d\n", dma_tr.size);
        $write("HDR: 0x%x\n", dma_header);
        $write("DATA (0x%x dwords):",(dma_tr.data.size/4));
        for (integer j=0; j < dma_tr.data.size; j++)
        begin
            if (j%32==0) $write("\n%4x:",j);
            if (j%8==0) $write(" ");
            $write("%x ",dma_tr.data[j]);
        end
        $write("\n");
    endtask
endclass

class Scoreboard;
    TransactionTable #(1)  scoreTable;
    ScoreboardGeneratorCbs generatorCbs;
    ScoreboardMonitorCbs   monitorCbs;
    ScoreboardDriverCbs    driverCbs;

    function new ();
        scoreTable   = new;
        generatorCbs = new(scoreTable);
        monitorCbs   = new(scoreTable);
        driverCbs    = new();
    endfunction

    task display();
        scoreTable.display();
    endtask
endclass
