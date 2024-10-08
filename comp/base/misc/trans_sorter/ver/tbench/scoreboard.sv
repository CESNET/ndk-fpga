//-- scoreboard.sv: Verification scoreboard.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
//--
//-- SPDX-License-Identifier: BSD-3-Clause
//--
//-- TODO - Implement BEHAVIOUR==1 functionality.

import sv_common_pkg::*;
import sv_mvb_pkg::*;

`include "idTable.sv"
`include "Confirmator.sv"

class ScoreboardRxTransDriverCbs extends DriverCbs;

    IdTable idTable;

    //  Creating interface that manage waiting for TRANS_FIFO_AFULL to be 0.
    protected virtual iAFull.tb vif;

    function new (IdTable it, virtual iAFull af);
        this.idTable    =it;
        this.vif             =af;
    endfunction

    //  Take transaction from generator, add ID and send transaction to DUT.
    virtual task pre_tx(ref Transaction transaction, string inst);
        MvbTransaction #(META_WIDTH) incomingTransaction;
        MvbTransaction #(ITEM_WIDTH) editedTransaction=new();
        bit assignedID=0;
        int transID;

        $cast(incomingTransaction,transaction);

        //  Waiting for signal FIFO_AFULL from component to be 0.
        while(vif.cb.FIFO_AFULL==1)begin
            //  Checking if the FIFO_AFULL signal is 0 every rising edge of CLK signal.
            @(vif.cb);
        end

        //  Copying basic information about transaction.
        editedTransaction.stream=incomingTransaction.stream;
        editedTransaction.word=incomingTransaction.word;
        editedTransaction.data[ITEM_WIDTH-1:ID_WIDTH]=incomingTransaction.data;

        //  Assigning ID for the transaction.
        transID=$urandom_range(2**ID_WIDTH-1,0);        //  Generating random ID.
        //  This loop will go on while the transaction wont have ID assigned.
        while(idTable.idTable[transID].status != 0)begin
            transID=$urandom_range(2**ID_WIDTH-1,0);    //  Generating random ID.
        end

        editedTransaction.data[ID_WIDTH-1:0]=transID;   //  If the status of transID is 0 then assign this ID to the transaction.
        if(VERBOSE_LEVEL>3)begin
            $timeformat(-9, 3, " ns", 8);
            $write("ID %1d was packed to the transaction %t\n",transID,$time);
        end

        transaction = editedTransaction;
    endtask

endclass


class ScoreboardRxConfsMonitorCbs extends MonitorCbs;

    tTransMbx   confsMbx;

    event transactionMoved;

    function new (tTransMbx cfmb, event wm);
        this.confsMbx           = cfmb;
        this.transactionMoved   = wm;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);

    endtask

    // -- Take transaction and passed them to confsMbx.. ----------------------
    //    Then trigger transactionMoved event
    virtual task post_rx(Transaction transaction, string inst);

        confsMbx.put(transaction);
        //  Trigger event that notify implementation that some word was moved.
        ->transactionMoved;
    endtask

endclass

class ScoreboardRxTransMonitorCbs extends MonitorCbs;

    tTransMbx   transMbx;

    event transactionMoved;

    function new (tTransMbx tmbx, event wm);
        this.transMbx           = tmbx;
        this.transactionMoved   = wm;
    endfunction

    virtual task pre_rx(ref Transaction transaction, string inst);

    endtask

    // -- Take transaction and passed them to transMbx. . ---------------------
    //    Then trigger transactionMoved event
    virtual task post_rx(Transaction transaction, string inst);
        $timeformat(-9, 3, " ns", 8);
        if(VERBOSE_LEVEL>2)begin
            $write("%t putting transaction to transMbx",$time);
            transaction.display();
        end
        transMbx.put(transaction);
        //  Trigger event that notify implementation that some word was moved.
        ->transactionMoved;
    endtask

endclass

class ScoreboardTxTransMonitorCbs extends MonitorCbs;

    TransactionTable #(1)   sc_table;
    IdTable                 idTable;

    function new (TransactionTable #(1) st, IdTable it);
        this.sc_table   = st;
        this.idTable    = it;
    endfunction

    // -- Take transaction remove it from the scoreTable  ---------------------
    //    and decresed counter in idTable at the ID of this transaction.
    virtual task post_rx(Transaction transaction, string inst);
        bit status=0;
        MvbTransaction #(ITEM_WIDTH) incomingTransaction;

        $cast(incomingTransaction,transaction);
        idTable.subFromCounter(incomingTransaction.data[ID_WIDTH-1:0]);

        sc_table.remove(transaction,status);
        if (status == 0)begin
            $write("Unknown transaction received from monitor %s\n", inst);
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            transaction.display();
            sc_table.display(1,"Test case scoreboard - ");
            $stop;
        end;
    endtask

endclass

class Scoreboard;

    protected virtual iAFull.tb vif;

    TransactionTable #(0)       transTable;
    TransactionTable #(1)       scoreTable;

    ScoreboardTxTransMonitorCbs txTransMonitorCbs;
    ScoreboardRxTransDriverCbs  rxTransDriverCbs;
    ScoreboardRxConfsMonitorCbs rxConfsMonitorCbs;
    ScoreboardRxTransMonitorCbs rxTransMonitorCbs;

    IdTable     idTable;
    tTransMbx   confsMbx;
    tTransMbx   confsInDUTMbx;
    tTransMbx   transMbx;
    Confirmator conf;

    event transactionMoved;


    function setEnabled();
        conf.setEnabled();
    endfunction

    function setDisabled();
        conf.setDisabled();
    endfunction

    function new (tTransMbx cmbx, virtual iAFull.tb af);
        this.confsMbx = cmbx;

        vif=af;

        //  Creating mailboxes.
        transMbx        = new();
        confsInDUTMbx   = new();

        //  Creating transactions tables.
        idTable     = new;
        scoreTable  = new;
        transTable  = new;

        //  Creating callbacks.
        txTransMonitorCbs   = new(scoreTable,idTable);
        rxTransDriverCbs    = new(idTable,vif);
        rxConfsMonitorCbs   = new(confsInDUTMbx,transactionMoved);
        rxTransMonitorCbs   = new(transMbx,transactionMoved);

        //  Creating object that is dedicated for implementation and generating
        //  confirmations.
        conf = new(idTable,confsMbx,transMbx,confsInDUTMbx,transactionMoved,transTable, scoreTable);
    endfunction

    task display();
        scoreTable.display(1,"Test case scoreboard - ");
    endtask

endclass
