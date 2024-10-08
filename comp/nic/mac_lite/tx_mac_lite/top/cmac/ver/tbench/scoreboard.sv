/* \scoreboard.sv
 * \brief Verification scoreboard
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2017
 */
/*
 * Copyright (C) 2017 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import sv_common_pkg::*;
import sv_lbus_pkg::*;
import sv_flu_pkg::*;
import sv_mi32_pkg::*;

class ScoreboardDriverCbs #(int behav=TR_TABLE_FIRST_ONLY) extends DriverCbs;

    TransactionTable #(behav) sc_table;

    function new (TransactionTable #(behav) st);
        sc_table = st;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
       FrameLinkUTransaction fluTrans;
       $cast(fluTrans, transaction);

       // Copy data and extend them to be at least 60B long
       if (fluTrans.data.size >= 60)
         begin
         sc_table.add(transaction);
       end
    endtask

endclass

class ScoreboardMonitorCbs #(int behav=TR_TABLE_FIRST_ONLY) extends MonitorCbs;

    TransactionTable #(behav) sc_table;
    longint total_bytes_cnt;

    function new (TransactionTable #(behav) st);
        this.sc_table        = st;
        this.total_bytes_cnt = 0;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        FrameLinkUTransaction fluTrans = new();
        LbusTransaction       lbusTrans;
        bit status=0;

        $cast(lbusTrans, transaction);
        // Transform FrameLink transaction into LBUS transaction
        lbustofluTransaction(fluTrans, lbusTrans);

        sc_table.remove(fluTrans, status);
        if (status==0)begin
            $write("Unknown transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
            sc_table.display();
            $stop;
        end;

        this.total_bytes_cnt = this.total_bytes_cnt + fluTrans.data.size + 4;

    endtask

    function void lbustofluTransaction(FrameLinkUTransaction fluTrans, LbusTransaction lbusTrans);
        fluTrans.data = lbusTrans.data;
    endfunction : lbustofluTransaction

endclass

class Scoreboard #(int behav = TR_TABLE_FIRST_ONLY);

    TransactionTable     #(behav) scoreTable;
    ScoreboardMonitorCbs #(behav) monitorCbs;
    ScoreboardDriverCbs  #(behav) driverCbs;

    function new ();
      scoreTable = new;
      monitorCbs = new(scoreTable);
      driverCbs  = new(scoreTable);
    endfunction

    task display();
      scoreTable.display();
      $write("Total Processed Bytes by Scoreboard:\t\t %10d\n", this.monitorCbs.total_bytes_cnt);
    endtask

endclass
