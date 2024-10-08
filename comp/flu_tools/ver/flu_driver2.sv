/*!
 * \file flu_driver2.sv
 * \brief Driver for FrameLinkUnaligned interface (different implementation)
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



class FrameLinkUDriver2 #(int pDataWidth=512, int pEopWidth=6, int pSopWidth=3) extends Driver;

    localparam REGIONS = 1;
    localparam REGION_SIZE = 1<<pSopWidth;
    localparam BLOCK_SIZE = (pDataWidth/8)/(1<<pSopWidth);
    localparam ITEM_WIDTH = (pDataWidth)/(1<<pEopWidth);
    localparam ITEMS = REGIONS * REGION_SIZE * BLOCK_SIZE;
    localparam REGION_ITEMS = REGION_SIZE * BLOCK_SIZE;
    localparam WORD_BLOCKS = REGIONS * REGION_SIZE;
    localparam SOF_POS_WIDTH = log2(REGION_SIZE);
    localparam EOF_POS_WIDTH = log2(REGION_SIZE * BLOCK_SIZE);
    typedef bit [ITEM_WIDTH-1 : 0] item;


    protected virtual iFrameLinkURx#(pDataWidth,pEopWidth,pSopWidth).tb vif;
    protected int offset = 0;
    protected item data[ITEMS];
    protected bit [REGIONS-1 : 0] sop;
    protected bit [REGIONS-1 : 0] eop;
    protected bit src_rdy;


    rand bit wordDelayEn;
    int wordDelayEnable_wt = 0;
    int wordDelayDisable_wt = 1;
    rand integer wordDelay;
    int wordDelayLow = 0;
    int wordDelayHigh = 0;

    rand bit ifgEn;
    int ifgEnable_wt = 3;
    int ifgDisable_wt = 1;
    rand integer ifg; // in blocks
    int ifgLow = 0;
    int ifgHigh = WORD_BLOCKS + WORD_BLOCKS - 1;

    constraint cDelays{
        wordDelayEn dist {1'b1 := wordDelayEnable_wt, 1'b0 := wordDelayDisable_wt};
        wordDelay inside { [wordDelayLow:wordDelayHigh] };
        ifgEn dist {1'b1 := ifgEnable_wt, 1'b0 := ifgDisable_wt};
        ifg inside { [ifgLow:ifgHigh] };
    }


    function new(string i, tTransMbx t, virtual iFrameLinkURx#(pDataWidth,pEopWidth,pSopWidth).tb v);
        super.new(i, t);
        vif = v;
        offset = 0;
        sop = 0;
        eop = 0;
        src_rdy = 0;
        vif.cb.SOP_POS <= 0;
        vif.cb.EOP_POS <= 0;
    endfunction

    task moveWord();
        vif.cb.DATA <= { << item {data} };
        vif.cb.SOP <= sop;
        vif.cb.EOP <= eop;
        vif.cb.SRC_RDY <= src_rdy;
        if(src_rdy) begin
            do
                @(vif.cb);
            while(!vif.cb.DST_RDY);
            vif.cb.SRC_RDY <= 0;
            IDLE_RANDOMIZE : assert(randomize());
            if(wordDelayEn)
                repeat(wordDelay)
                    @(vif.cb);
        end else
            @(vif.cb);
        for (int r = 0; r < REGIONS; r++) begin
            vif.cb.SOP_POS[r*SOF_POS_WIDTH +: SOF_POS_WIDTH] <= $urandom_range((REGION_SIZE-1),0);
            vif.cb.EOP_POS[r*EOF_POS_WIDTH +: EOF_POS_WIDTH] <= $urandom_range((REGION_ITEMS-1),0);
        end
        sop = 0;
        eop = 0;
        src_rdy = 0;
        offset = 0;
    endtask

    task moveBlock();
        offset = offset + BLOCK_SIZE;
        if(offset >= ITEMS)
            moveWord();
    endtask

    task run();
        Transaction transaction;
        FrameLinkUTransaction tr;
        int i, j, r, p;
        @(vif.cb); // initial sync
        while(enabled) begin
            while(transMbx.try_get(transaction) == 0) begin // wait for transaction
                moveWord();
                busy = 0;
                if (!enabled) return;
            end
            busy = 1;
            IDLE_RANDOMIZE : assert(randomize()); // Inter Frame Gap
            if(ifgEn)
                repeat(ifg)
                    moveBlock();
            foreach(cbs[i]) cbs[i].pre_tx(transaction, inst); // notify callbacks
            $cast(tr, transaction);
            while(sop[offset / REGION_ITEMS]) // two SOFs not allowed in the same region
                moveBlock();
            while(eop[(offset + tr.data.size - 1) / REGION_ITEMS]) // two EOFs not allowed in the same region
                moveBlock();
            r = offset / REGION_ITEMS; p = offset % REGION_ITEMS; // mark SOF
            sop[r] = 1;
            if(SOF_POS_WIDTH)
                vif.cb.SOP_POS[r*SOF_POS_WIDTH +: SOF_POS_WIDTH] <= p / BLOCK_SIZE;
            i = 0;
            while(i < tr.data.size)// transaction written onto bus
                if(offset == 0 && (tr.data.size-i) > ITEMS) begin
                    data = tr.data[i +: ITEMS];
                    src_rdy = 1;
                    moveWord();
                    i = i + ITEMS;
                end else if((tr.data.size-i) > BLOCK_SIZE) begin
                    data[offset +: BLOCK_SIZE] = tr.data[i +: BLOCK_SIZE];
                    src_rdy = 1;
                    moveBlock();
                    i = i + BLOCK_SIZE;
                end else begin // last block
                    for(j = 0; i < tr.data.size; j++, i++)
                        data[offset+j] = tr.data[i];
                    src_rdy = 1;
                    r = offset / REGION_ITEMS; p = offset % REGION_ITEMS; // mark EOF
                    eop[r] = 1;
                    if(EOF_POS_WIDTH)
                        vif.cb.EOP_POS[r*EOF_POS_WIDTH +: EOF_POS_WIDTH] <= p + j - 1;
                    foreach(cbs[i]) cbs[i].post_tx(transaction, inst);
                    moveBlock();
                    break;
                end
        end
    endtask

endclass
