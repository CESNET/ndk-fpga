/* scoreboard.sv: scoreboard
 * Copyright (C) 2024 BrnoLogic, Ltd.
 * Author(s): Radek Hajek <hajek@brnologic.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import sv_common_pkg::*;
import sv_mfb_pkg::*;
import sv_axi_pkg::*;

class ScoreboardDriverCbs extends DriverCbs;

    TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;

    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) st);
        sc_table = st;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
        MfbTransaction #(ITEM_WIDTH) t_mfb;
        AxiTransaction #(8) t_axi; // AXI is always byte oriented

        t_axi = new;

        $cast(t_mfb, transaction);

        // conversion from MFB (any ITEM_WIDTH) to AXI(8)
        t_axi.data = {<<8{ {<<ITEM_WIDTH{t_mfb.data}} }};
        sc_table.add(t_axi);

    endtask

    virtual task post_tx(Transaction transaction, string inst);
    endtask

endclass

class ScoreboardMonitorCbs extends MonitorCbs;

    TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;

    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) st);
        this.sc_table = st;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        bit status=0;
        sc_table.remove(transaction, status);
        if (status==0)begin
            $write("Unknown transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
            sc_table.display();
            $stop;
        end;
    endtask

endclass

class Scoreboard;

    TransactionTable #(TR_TABLE_FIRST_ONLY) scoreTable;
    ScoreboardMonitorCbs  monitorCbs;
    ScoreboardDriverCbs   driverCbs;

    function new ();
      scoreTable = new;
      monitorCbs = new(scoreTable);
      driverCbs  = new(scoreTable);
    endfunction

    task display();
      scoreTable.display();
    endtask

    task is_empty(output bit empty);
        empty = $size(scoreTable.tr_table) == 0;
    endtask

endclass
