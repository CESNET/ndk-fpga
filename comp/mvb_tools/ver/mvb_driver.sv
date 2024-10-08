/*!
 * \file mvb_driver.sv
 * \brief Driver for Multi-Value Bus interface
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



class MvbDriver #(ITEMS = 4, ITEM_WIDTH = 8) extends Driver;

    typedef logic [ITEM_WIDTH-1 : 0] item;


    protected virtual iMvbRx#(ITEMS,ITEM_WIDTH).tb vif;
    protected int offset = 0;
    protected item data[ITEMS];
    protected bit [ITEMS-1 : 0] vld;
    protected bit src_rdy;
    protected int unsigned word;

    // Source ready delay parameters for whole invalid words
    rand bit wordDelayEn;
    rand integer wordDelay;
    int wordDelayEnable_wt = 10;  // Enable/Disable word delay weights.
    int wordDelayDisable_wt = 90; // Chance to insert word delay has a ratio of Enable_wt : Disable_wt.
    int wordDelayLow = 0;        // Length limits of word delay in number of cycles, High value should not be lower then Low value.
    int wordDelayHigh = 50;       // Used only during enabled delay, length of zero leads to skipped delay even though it was enabled.

    // Parameters of delay (gaps) between individual MVB items.
    rand bit ivgEn;
    rand integer ivg;
    int ivgEnable_wt = 3;  // Enable/Disable gaps between items.
    int ivgDisable_wt = 1; // Chance to insert gap has a ratio of Enable_wt : Disable_wt.
    int ivgLow = 0;        // Length limits of gep in number of invalid items, High value should not be lower then Low value.
    int ivgHigh = ITEMS + ITEMS - 1; // Used only during enabled gap, length of zero leads to no gap even though it was enabled.

    // Operation mode for invalid data items and words.
    localparam MODE_NOCHANGE = 0;   // Values of invalid items are retained from previous cycles.
    localparam MODE_ZERO = 1;       // Invalid items has always a value of zero. Also, valid signal is always zero during invalid words (when SRC_RDY is 0).
    localparam MODE_RANDOM = 2;     // Values of invalid items are always set to random values. Also, valid signal has a random value during invalid words (when SRC_RDY is 0).
    localparam MODE_UNDEFINED = 3;  // Values of invalid items are always set to 'X' values. Also, valid signal bits has 'X' values during invalid words (when SRC_RDY is 0).
    int mode = MODE_RANDOM; // Set this variable to one of the modes above. It can be changed any time during simulation.

    constraint cDelays{
        wordDelayEn dist {1'b1 := wordDelayEnable_wt, 1'b0 := wordDelayDisable_wt};
        wordDelay inside { [wordDelayLow:wordDelayHigh] };
        ivgEn dist {1'b1 := ivgEnable_wt, 1'b0 := ivgDisable_wt};
        ivg inside { [ivgLow:ivgHigh] };
    }


    function new(string i, tTransMbx t, virtual iMvbRx#(ITEMS,ITEM_WIDTH).tb v);
        super.new(i, t);
        vif = v;
        offset = 0;
        vif.cb.VLD <= 0;
        src_rdy = 0;
        word = 0;
    endfunction

    function void fillEmptyWord();
        if(mode == MODE_ZERO) begin
            vif.cb.DATA <= 0;
            vif.cb.VLD <= 0;
        end else if(mode == MODE_RANDOM) begin
            DATA_RANDOMIZE1 : assert(std::randomize(data,vld));
            vif.cb.DATA <= { << item {data} };
            vif.cb.VLD <= vld;
        end else if(mode == MODE_UNDEFINED) begin
            vif.cb.DATA <= 'X;
            vif.cb.VLD <= 'X;
        end
    endfunction

    task moveWord();
        if(src_rdy) begin
            vif.cb.DATA <= { << item {data} };
            vif.cb.SRC_RDY <= src_rdy;
            do
                @(vif.cb);
            while(!vif.cb.DST_RDY);
            vif.cb.SRC_RDY <= 0;
            IDLE_RANDOMIZE1 : assert(randomize());
            if(wordDelayEn)
                repeat(wordDelay) begin
                    fillEmptyWord();
                    vif.cb.SRC_RDY <= 1'b0;
                    @(vif.cb);
                end
            word = word + 1;
        end else begin
            fillEmptyWord();
            vif.cb.SRC_RDY <= 1'b0;
            @(vif.cb);
        end
        vif.cb.VLD <= 0;
        src_rdy = 0;
        offset = 0;
    endtask

    task moveItem();
        offset = offset + 1;
        if(offset >= ITEMS)
            moveWord();
    endtask

    task run();
        Transaction transaction;
        MvbTransaction #(ITEM_WIDTH) tr;
        fillEmptyWord();
        vif.cb.SRC_RDY <= 0;
        @(vif.cb); // initial sync
        vif.cb.VLD <= 0;
        while(enabled) begin
            while(transMbx.try_get(transaction) == 0) begin // wait for transaction
                moveWord();
                busy = 0;
                if (!enabled) return;
            end
            busy = 1;
            IDLE_RANDOMIZE2 : assert(randomize()); // Inter Value Gap
            if(ivgEn)
                repeat(ivg) begin
                    if(mode == MODE_ZERO)
                        data[offset] = 0;
                    else if(mode == MODE_RANDOM)
                        DATA_RANDOMIZE3 : assert(std::randomize(data[offset]));
                    else if(mode == MODE_UNDEFINED)
                        data[offset] = 'X;
                    moveItem();
                end
            foreach(cbs[i]) cbs[i].pre_tx(transaction, inst); // notify callbacks
            $cast(tr, transaction);
            data[offset] = tr.data;
            vif.cb.VLD[offset] <= 1;
            src_rdy = 1;
            tr.stream = offset;
            tr.word = word;
            foreach(cbs[i]) cbs[i].post_tx(transaction, inst);
            moveItem();
        end
    endtask

endclass
