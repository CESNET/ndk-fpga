/* scoreboard.sv: scoreboard
 * Copyright (C) 2024 DynaNIC Semiconductors, Ltd.
 * Author(s): Radek Hajek <hajek@dyna-nic.com>
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

    // Convert a packet's AXI byte stream into MFB ITEM_WIDTH-bit items.
    //
    // Inputs:
    //   bytes[]     - dynamic array of 8-bit bytes; one AXI packet's full payload.
    // Outputs:
    //   item_data[] - dynamic array of ITEM_WIDTH-bit words; the same packet
    //                 repacked into MFB items.
    // Assumption: ITEM_WIDTH is a multiple of 8.
    function automatic void data_bytes_to_items(input bit [7:0] bytes[],
                                                output bit [ITEM_WIDTH-1:0] item_data[]);
        int byte_count = bytes.size();
        int bytes_per_item = ITEM_WIDTH / 8;
        int item_count;

        // Number of MFB items needed = ceiling(byte_count / bytes_per_item).
        item_count = (byte_count + bytes_per_item - 1) / bytes_per_item;
        item_data = new[item_count];

        for (int item = 0; item < item_count; item++) begin
            item_data[item] = '0;
            for (int byte_in_item = 0; byte_in_item < bytes_per_item; byte_in_item++) begin
                int byte_idx = item * bytes_per_item + byte_in_item;
                if (byte_idx < byte_count) begin
                    // Place byte number byte_idx of the packet into bits
                    // [byte_in_item*8+7 : byte_in_item*8] of the MFB item.
                    item_data[item][byte_in_item*8 +: 8] = bytes[byte_idx];
                end
            end
        end
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
        AxiTransaction #(8, AXI_USER_WIDTH) t_axi;
        MfbTransaction #(ITEM_WIDTH, META_WIDTH) t_mfb;
        t_mfb = new;

        $cast(t_axi, transaction);
        data_bytes_to_items(t_axi.data, t_mfb.data);
        t_mfb.meta = t_axi.user;
        // Enable Meta Signal Comparison
        t_mfb.check_meta = 1'b1;

        sc_table.add(t_mfb);
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
