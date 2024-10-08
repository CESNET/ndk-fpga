//-- scoreboard.sv: Verification scoreboard.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
//--
//-- SPDX-License-Identifier: BSD-3-Clause

import sv_mvb_pkg::*;

class  PointerMover;

    TransactionTable #(0) acceptedTransaction;
    protected virtual iPtr.tb PTR_INT;
    bit enabled;

    function new (TransactionTable #(0) at, virtual iPtr.tb ptr);
        acceptedTransaction = at;
        PTR_INT             = ptr;
    endfunction

    function setEnabled();
        this.enabled=1;
        fork
            run();
        join_none;
    endfunction

    function setDisabled();
        this.enabled=0;
    endfunction


    //task run();
    //    logic [SPACE_GLB_PTR-1:0]    spaceGlbRdPtr = 0;
    //    int unsigned read_size;
    //    time rand_delay;

    //    while (enabled==1 || spaceGlbRdPtr != PTR_INT.cb.SPACE_GLB_WR_PTR) begin
    //        // -- Waiting for rising edge of CLK signal
    //        rand_delay = $urandom_range(200ns, 0ns);
    //        #(rand_delay);

    //        read_size = $urandom_range((unsigned'(PTR_INT.cb.SPACE_GLB_WR_PTR) - spaceGlbRdPtr) & (2**SPACE_GLB_PTR-1));
    //        spaceGlbRdPtr = spaceGlbRdPtr + read_size;
    //        @(PTR_INT.cb);
    //        PTR_INT.cb.SPACE_GLB_RD_PTR <= spaceGlbRdPtr;
    //    end
    //endtask

    task run();
        logic [SPACE_GLB_PTR-1:0]    spaceGlbRdPtr = 0;
        int unsigned raw_size;
        int unsigned read_size;

        @(PTR_INT.cb);
        @(PTR_INT.cb);

        while (enabled==1 || spaceGlbRdPtr != PTR_INT.cb.SPACE_GLB_WR_PTR) begin
            int numOfPacketToRemove = MAX_NUMBER_OF_PACKETS_TO_BE_REMOVED;// $urandom_range(MAX_NUMBER_OF_PACKETS_TO_BE_REMOVED, 0);
            logic [SPACE_GLB_PTR-1:0]    spaceGlbRdPtr = 0;

            // -- Waiting for rising edge of CLK signal
            if(VERBOSE_LEVEL>5) begin
                $timeformat(-9, 3, " ns", 8);
                $write("%t Number of packets to be removed in this CLK: %d\n",$time,numOfPacketToRemove);
            end

            //for (int i = 0; i < numOfPacketToRemove && acceptedTransaction.tr_table.size > 0 ; i++) begin
            while (acceptedTransaction.tr_table.size() > 0) begin
                int unsigned raw_size;
                MvbTransaction #(TX_GLOBAL_ITEM_WIDTH) oldestTr;
                bit roundUpFlag = 0, status = 0;

                $cast(oldestTr, acceptedTransaction.tr_table[0]);
                // -- Counting end of packet
                raw_size = unsigned'(oldestTr.data[ADDRES_WIDTH-1 -: ADDRES_WIDTH]) + unsigned'(oldestTr.data[LEN+ADDRES_WIDTH-1 -: LEN]);
                spaceGlbRdPtr = (raw_size + ADRESS_ALIGNMENT -1)/ADRESS_ALIGNMENT;
                //spaceGlbRdPtr = spaceGlbRdPtr + (raw_size + ADRESS_ALIGNMENT -1)/ADRESS_ALIGNMENT;

                if(VERBOSE_LEVEL>4)begin
                    oldestTr.display();
                    $write("ADDR %b\nLEN %b\n",oldestTr.data[ADDRES_WIDTH-1:0],oldestTr.data[LEN+ADDRES_WIDTH-1:ADDRES_WIDTH]);
                end
                // -- Round up addres to ADRESS_ALIGNMENT and shift addres by sqrt(ADDRESS_ALIGMENT) to right (in the addrOfActualPacket is end of packet align to ADRESS_ALIGNMENT)
                //addrOfActualPacket = (addrOfActualPacket + ADRESS_ALIGNMENT -1)/ADRESS_ALIGNMENT;
                // -- End of round up

                acceptedTransaction.remove(oldestTr,status);
            end
            // -- Assigning the result of the calculation to the SPACE_GLB_RD_PTR input of the DUT
            @(PTR_INT.cb);
            PTR_INT.cb.SPACE_GLB_RD_PTR <= PTR_INT.cb.SPACE_GLB_WR_PTR;
            // -- And remove the Transaction from transaction table
        end
    endtask
endclass

class ScoreboardDriverCbs extends DriverCbs;

    TransactionTable #(0) globalScoreTable;
    TransactionTable #(0) streamScoreTable;

    function new (TransactionTable #(0) gst, TransactionTable #(0) sst);
        globalScoreTable = gst;
        streamScoreTable = sst;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask

    virtual task post_tx(Transaction transaction, string inst);
        if(VERBOSE_LEVEL > 0)begin
            $timeformat(-9, 3, " ns", 8);
            $write("%t New transaction on the input interface : ",$time);
            transaction.display();
        end
        // -- Adding transaction to both scoreboard (to be able to implement different functionality for the inputs)
        globalScoreTable.add(transaction);
        streamScoreTable.add(transaction);
    endtask

endclass

class ScoreboardStreamsMonitorCbs extends MonitorCbs;

    TransactionTable #(0) sc_table;

    function new (TransactionTable #(0) st);
        this.sc_table = st;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        MvbTransaction #(TX_GLOBAL_ITEM_WIDTH) incomingTransaction=new;
        MvbTransaction #(RX_ITEM_WIDTH) toBeRemoved=new;
        bit status=0;

        $cast(incomingTransaction,transaction);

        // -- Assigning informations of the incoming transaction to new transaction with space for adress
        toBeRemoved.word=incomingTransaction.word;
        toBeRemoved.stream=incomingTransaction.stream;
        toBeRemoved.data[RX_ITEM_WIDTH-1:LEN]=incomingTransaction.data[TX_GLOBAL_ITEM_WIDTH-1:ADDRES_WIDTH+LEN];
        toBeRemoved.data[LEN-1:0]=incomingTransaction.data[LEN+ADDRES_WIDTH-1:ADDRES_WIDTH];

        if(VERBOSE_LEVEL > 0) begin
            $timeformat(-9, 3, " ns", 8);
            $write("%t New transaction on the output interface : ",$time);
            toBeRemoved.display();
        end

        // -- Test for checking if the address is align to ADRESS_ALIGNMENT
        if(incomingTransaction.data[ADDRES_WIDTH-1:0]%ADRESS_ALIGNMENT!=0)begin
            $write("Packet is not aligned\n");
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            incomingTransaction.display();
            sc_table.display();
            $stop;
        end

        sc_table.remove(toBeRemoved, status);
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

class ScoreboardGlobalMonitorCbs extends MonitorCbs;

    TransactionTable #(0) sc_table;
    TransactionTable #(0) acceptedTransaction;

    function new (TransactionTable #(0) st, TransactionTable #(0) at);
        this.sc_table = st;
        acceptedTransaction = at;
    endfunction

    virtual task post_rx(Transaction transaction, string inst);
        MvbTransaction #(TX_GLOBAL_ITEM_WIDTH) incomingTransaction=new;
        MvbTransaction #(RX_ITEM_WIDTH) toBeRemoved=new;
        bit status=0;

        $cast(incomingTransaction,transaction);

        // -- Assigning informations of the incoming transaction to new transaction with space for adress
        toBeRemoved.word=incomingTransaction.word;
        toBeRemoved.stream=incomingTransaction.stream;
        toBeRemoved.data[RX_ITEM_WIDTH-1:LEN]=incomingTransaction.data[TX_GLOBAL_ITEM_WIDTH-1:ADDRES_WIDTH+LEN];
        toBeRemoved.data[LEN-1:0]=incomingTransaction.data[LEN+ADDRES_WIDTH-1:ADDRES_WIDTH];

        if(VERBOSE_LEVEL > 0) begin
            $timeformat(-9, 3, " ns", 8);
            $write("%t New transaction on the output interface : ",$time);
            toBeRemoved.display();
        end

        // -- Test for checking if the address is align to ADRESS_ALIGNMENT
        if(incomingTransaction.data[ADDRES_WIDTH-1:0]%ADRESS_ALIGNMENT!=0)begin
            $write("Packet is not aligned\n");
            $timeformat(-9, 3, " ns", 8);
            $write("Time: %t\n", $time);
            incomingTransaction.display();
            sc_table.display();
            $stop;
        end

        // -- Test for checking if there is at least MINIMAL_GAP_SIZE space between packets
        acceptedTransaction.lock();
        foreach(acceptedTransaction.tr_table[i])begin
            MvbTransaction #(TX_GLOBAL_ITEM_WIDTH) tr = new;
            $cast(tr,acceptedTransaction.tr_table[i]);
            if(VERBOSE_LEVEL>3) begin
                $write("Address of actual packet %d : %d and lenght of this packet :%d\n",i,tr.data[ADDRES_WIDTH-1:0],tr.data[LEN+ADDRES_WIDTH-1:ADDRES_WIDTH]);
                $write("Address of incomming packet %d : %d and lenght of this packet :%d\n",i,incomingTransaction.data[ADDRES_WIDTH-1:0],incomingTransaction.data[LEN+ADDRES_WIDTH-1:ADDRES_WIDTH]);
            end
            // -- Checking which packet has lower adress
            if (tr.data[ADDRES_WIDTH-1:0] < incomingTransaction.data[ADDRES_WIDTH-1:0]) begin
                // -- Checking the gap
                if (MINIMAL_GAP_SIZE > incomingTransaction.data[ADDRES_WIDTH-1:0]-tr.data[ADDRES_WIDTH-1:0]-tr.data[LEN+ADDRES_WIDTH-1:ADDRES_WIDTH]) begin
                    $write("Bap between packets is too short\n");
                    $timeformat(-9, 3, " ns", 8);
                    $write("Time: %t\n", $time);
                    incomingTransaction.display();
                    tr.display();
                    sc_table.display();
                    $stop;
                end
            end else begin
                // -- Checking the gap
                if (MINIMAL_GAP_SIZE > tr.data[ADDRES_WIDTH-1:0]-incomingTransaction.data[ADDRES_WIDTH-1:0]-incomingTransaction.data[LEN+ADDRES_WIDTH-1:ADDRES_WIDTH]) begin
                    $write("Bap between packets is too short\n");
                    $timeformat(-9, 3, " ns", 8);
                    $write("Time: %t\n", $time);
                    incomingTransaction.display();
                    tr.display();
                    sc_table.display();
                    $stop;
                end
            end
        end
        acceptedTransaction.unlock();

        acceptedTransaction.add(incomingTransaction);

        sc_table.remove(toBeRemoved, status);
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

    TransactionTable #(0) globalScoreTable;
    TransactionTable #(0) streamScoreTable;
    TransactionTable #(0) acceptedTransaction;
    ScoreboardDriverCbs streamDriverCbs;
    ScoreboardStreamsMonitorCbs streamMonitorCbs;
    ScoreboardGlobalMonitorCbs globalMonitorCbs;

    protected virtual iPtr.tb PTR_INT;

    PointerMover ptrMov;


    function new (virtual iPtr.tb ptr);
        PTR_INT             = ptr;
        globalScoreTable    = new;
        streamScoreTable    = new;
        acceptedTransaction = new;
        ptrMov              = new(acceptedTransaction, PTR_INT);
        streamDriverCbs     = new(globalScoreTable, streamScoreTable);
        streamMonitorCbs    = new(streamScoreTable);
        globalMonitorCbs    = new(globalScoreTable, acceptedTransaction);
    endfunction

    task wait_for();
        int unsigned timeout = 0;

        fork
            begin #(10000*CLK_PERIOD); timeout = 1; end
            begin wait((!GLOBAL_OUTPUT_EN || globalScoreTable.tr_table.size() == 0) && (!STREAM_OUTPUT_EN || streamScoreTable.tr_table.size() == 0)); end
        join_any

        if (timeout) begin
            $error("Design is probubly stack. Timeout on end of verification\n");
            $strop();
        end
    endtask

    task display();
        if(GLOBAL_OUTPUT_EN) begin
            globalScoreTable.display(1,"Global Score Table");
        end
        if(STREAM_OUTPUT_EN) begin
            streamScoreTable.display(1, "Stream Score Table");
        end

        if ((GLOBAL_OUTPUT_EN && globalScoreTable.tr_table.size() != 0) || (STREAM_OUTPUT_EN && streamScoreTable.tr_table.size() != 0)) begin
            $error("Transaction tables is not empty\n");
            $stop();
        end
    endtask
endclass
