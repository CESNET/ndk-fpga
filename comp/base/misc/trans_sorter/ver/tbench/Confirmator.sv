//-- Confirmator.sv: Object for verification of trans_sorter.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
//--
//-- SPDX-License-Identifier: BSD-3-Clause

// -- This class is designed to send confirmation transactions ----------------
//    to mailbox of confsDriver. And also handle implementation
//    of the component.
class  Confirmator;

    tTransMbx   confsMbx;
    tTransMbx   confsInDUTMbx;
    tTransMbx   transMbx;
    IdTable     idTable;
    bit         enabled;
    event       transactionMoved;

    TransactionTable #(0)       transTable;
    TransactionTable #(1)       scoreTable;

    function new (IdTable it, tTransMbx cmbx, tTransMbx tmbx, tTransMbx cidutmbx, event wm, TransactionTable #(0) tt, TransactionTable #(1) st);
        this.idTable            =it;
        this.confsMbx           =cmbx;
        this.confsInDUTMbx      =cidutmbx;
        this.transMbx           =tmbx;
        this.transactionMoved   =wm;
        this.transTable         =tt;
        this.scoreTable         =st;
    endfunction

    function setEnabled();
        enabled=1;
        //  Start implementation and generator processes.
        fork
            runGeneratorOfConformations();
            runImplementationOfDUT();
        join_none;
    endfunction

    function setDisabled();
        enabled=0;
    endfunction

    //  This task handle generating confirmations for DUT and sends them after a random delay.
    //  Before sending confirmation to DUT, this task wait for random delay.
    task runGeneratorOfConformations();
        while (enabled==1) begin
            //  Generating variables that determine the course of the process.
            int delayBetweenConfirmations   = $urandom_range(DELAY_BETWEEN_CONFS_HIGH, DELAY_BETWEEN_CONFS_LOW);
            int numberOfConfTransaction     = $urandom_range(NUMBER_OF_TRANS_HIGH, NUMBER_OF_TRANS_LOW);

            //  Delay between generating confirmations.
            #((delayBetweenConfirmations*CLK_PERIOD));

            //  Generate "numberOfConfTransaction" confirmations.
            while(numberOfConfTransaction>0)begin
                bit status=0;
                int delayToSendConf = $urandom_range(DELAY_TO_SEND_CONFS_HIGH, DELAY_TO_SEND_CONFS_LOW);      //  Generate delay between generate and send of confirmations.
                int ID              = $urandom_range(2**ID_WIDTH-1,0);     //  Generated ID.

                idTable.setCounterToConfState(ID,status);     //  Set up this ID to confirmation state.

                //  Send generated ID.
                if(status==1)begin

                    MvbTransaction #(ID_WIDTH) confsTrans=new();

                    if(VERBOSE_LEVEL>2)begin
                        $write("- idTable for id %1d --------------------------------------\n", ID);
                        idTable.display();
                        $write("------------------------------------------------------------\n");
                    end
                    //  Waiting to send confirmation.
                    #(delayToSendConf*CLK_PERIOD);
                    confsTrans.data=ID;
                    //  Send confirmation.
                    confsMbx.put(confsTrans);
                end

                numberOfConfTransaction-=1;
            end
        end
    endtask

    // -- This task will confirm transaction with same ID as is in the confirmationID. ----------------------------------------------------------------
    //  The MvbTransaction confirmationID containts ID that is being confirmed.
    task confirmTrWithSameID(MvbTransaction #(ID_WIDTH) confirmationID);
        for(int i=0 ; i < transTable.tr_table.size ; i++) begin
            MvbTransaction #(ITEM_WIDTH+1) actualTransaction=new();
            transTable.tr_table[i].copy(actualTransaction);
            //  Only if the IDs are the same is the LSB set to 1.
            if(actualTransaction.data[ID_WIDTH:1]==confirmationID.data)begin
                actualTransaction.data[0]=1;
                actualTransaction.copy(transTable.tr_table[i]);
            end
        end
    endtask

    //  This task remove already confirmed transactions from the component. -------------------------------------------------------------------------
    task removeAlreadyConfTrInOrder();
        //  Check all transactions while they are confirmed.
        for (int k=0 ; k < transTable.tr_table.size ; k++) begin
            MvbTransaction #(ITEM_WIDTH+1) actualTransaction=new();

            transTable.tr_table[k].copy(actualTransaction);
            //  Remove only confirmed transactions.
            if(actualTransaction.data[0]==1)begin
                bit status=0;
                MvbTransaction #(ITEM_WIDTH) transactionToScoreTable=new();

                //  Setting transaction variables.
                transactionToScoreTable.data=actualTransaction.data[ITEM_WIDTH:1];
                transactionToScoreTable.word=actualTransaction.word;
                transactionToScoreTable.stream=actualTransaction.stream;

                //  Add transaction to scoreTable and remove it from transTable.
                scoreTable.add(transactionToScoreTable);
                transTable.remove(actualTransaction,status);

                if(VERBOSE_LEVEL>0)begin
                    $timeformat(-9, 3, " ns", 8);
                    $write("Transaction 0x%1b added to scoreTable and transaction 0x%1b was removed form transTable %t\n", transactionToScoreTable.data, actualTransaction.data-1,$time);
                end
                k--;
            end else if (actualTransaction.data[0]==0) begin
                //  Breake the for loop if the actual transaction is not confirmed.
                break;
            end
        end
    endtask

    // -- Implementation of the component. ------------------------------------------------------------------------------------------------------------
    //    This task implements the acceptance of transactions and confirmation of the transacrion in that order.
    //    This process happens only if some word was moved at any input interface.
    task runImplementationOfDUT();
        while (enabled==1) begin
            Transaction tr;

            //  Waiting for transaction to be moved.
            @(transactionMoved);
            //  Trying to get transactions from mailbox dedicated for transactions.
            while(transMbx.try_get(tr)!=0)begin

                MvbTransaction #(ITEM_WIDTH) incomingTransaction        =new();
                MvbTransaction #(ITEM_WIDTH+1) transactionWithConfBit   =new();

                if(VERBOSE_LEVEL>2)begin
                    $timeformat(-9, 3, " ns", 8);
                    $write("%t transaction in mailbox- ",$time);
                    tr.display();
                end
                tr.copy(incomingTransaction);
                //  Setting transaction variables.
                transactionWithConfBit.data[0]=0;
                transactionWithConfBit.data[ITEM_WIDTH:1]=incomingTransaction.data;
                transactionWithConfBit.stream=incomingTransaction.stream;
                transactionWithConfBit.word=incomingTransaction.word;

                //  Increase the value of the counter that holds the number of transactions with this ID that are currently in the component.
                idTable.addToCounter(transactionWithConfBit.data[ID_WIDTH:1]);
                //  Add this transactions to the transTable that holds transactions that are currently in the component.
                transTable.add(transactionWithConfBit);
                if(VERBOSE_LEVEL>0)begin
                    $timeformat(-9, 3, " ns", 8);
                    $write("Transaction 0x%b added to transTable %t\n", transactionWithConfBit.data,$time);
                end
                if (VERBOSE_LEVEL>1) begin
                    transTable.display(1, "transTable with new item - ");
                end
            end

            //  Trying to get transactions from mailbox dedicated for confirmations.
            while(confsInDUTMbx.try_get(tr)!=0)begin
                MvbTransaction #(ID_WIDTH) confirmationID=new();
                bit status=0;

                tr.copy(confirmationID);
                if(VERBOSE_LEVEL>0)begin
                    $timeformat(-9, 3, " ns", 8);
                    $write("ID 0x%b at confirmation interface %t\n", confirmationID.data, $time);
                end

                if (VERBOSE_LEVEL>3) begin
                    transTable.display(1,"Transaction in transTable - ");
                end
                //  Confirm and remove transactions only if there are any transactions with the ID that is currently confirmed.
                if(idTable.idTable[confirmationID.data].idCount==0)begin
                    idTable.idTable[confirmationID.data].status=0;
                    if (VERBOSE_LEVEL>1) begin
                        $write("Change status of id %d to 0\n",confirmationID.data);
                    end
                end else begin
                    confirmTrWithSameID(confirmationID);
                    removeAlreadyConfTrInOrder();

                    if (VERBOSE_LEVEL>1) begin
                        transTable.display(1,"transTable after confirmation - ");
                    end

                end

            end
        end
    endtask

endclass
