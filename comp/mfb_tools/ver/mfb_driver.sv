/*!
 * \file mfb_driver.sv
 * \brief Driver for Multi-Frame Bus interface
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 */



class MfbDriver #(REGIONS = 4, REGION_SIZE = 8, BLOCK_SIZE = 8, ITEM_WIDTH = 8, SOF_CTRL = 0, META_WIDTH = 1, META_ALIGNMENT = 0) extends Driver;
    // META_WIDTH defines width META signal in bits per region.
    // META_ALIGNMENT=0 => META signal is aligned with SOF, META_ALIGNMENT=1 => META signal is aligned with EOF.

    localparam ITEMS = REGIONS * REGION_SIZE * BLOCK_SIZE;
    localparam REGION_ITEMS = REGION_SIZE * BLOCK_SIZE;
    localparam WORD_BLOCKS = REGIONS * REGION_SIZE;
    localparam SOF_POS_WIDTH = log2(REGION_SIZE);
    localparam EOF_POS_WIDTH = log2(REGION_SIZE * BLOCK_SIZE);
    typedef logic [ITEM_WIDTH-1 : 0] item;
    typedef logic [META_WIDTH-1 : 0] meta_item;


    protected virtual iMfbRx#(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,META_WIDTH).tb vif;
    protected int offset = 0;
    protected item data[ITEMS];
    protected meta_item meta[REGIONS];
    protected bit [REGIONS-1 : 0] sof;
    protected bit [REGIONS-1 : 0] eof;
    protected bit [REGIONS*SOF_POS_WIDTH-1 : 0] sof_pos;
    protected bit [REGIONS*EOF_POS_WIDTH-1 : 0] eof_pos;
    protected bit src_rdy;

    // Source ready delay parameters for whole invalid words
    rand bit wordDelayEn;
    int wordDelayEnable_wt = 10;
    int wordDelayDisable_wt = 90;
    rand integer wordDelay;
    int wordDelayLow = 0;
    int wordDelayHigh = 50;

    // Parameters of delay (gaps) between individual MFB packets.
    rand bit ifgEn;
    int ifgEnable_wt = 3;
    int ifgDisable_wt = 1;
    rand integer ifg; // in blocks
    int ifgLow = 0;
    int ifgHigh = WORD_BLOCKS + WORD_BLOCKS - 1;

    // Operation mode for invalid data items and words.
    localparam MODE_NOCHANGE = 0;   // Values of invalid data items and values are retained from previous cycles.
    localparam MODE_ZERO = 1;       // Invalid items and values has always a value of zero.
    localparam MODE_RANDOM = 2;     // Invalid items and values are always set to random values.
    localparam MODE_UNDEFINED = 3;  // Invalid items are values are always set to 'X'.
    int mode = MODE_RANDOM; // Set this variable to one of the modes above. It can be changed any time during simulation.

    constraint cDelays{
        wordDelayEn dist {1'b1 := wordDelayEnable_wt, 1'b0 := wordDelayDisable_wt};
        wordDelay inside { [wordDelayLow:wordDelayHigh] };
        ifgEn dist {1'b1 := ifgEnable_wt, 1'b0 := ifgDisable_wt};
        ifg inside { [ifgLow:ifgHigh] };
    }


    function new(string i, tTransMbx t, virtual iMfbRx#(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,META_WIDTH).tb v);
        super.new(i, t);
        vif = v;
        offset = 0;
        sof = 0;
        eof = 0;
        src_rdy = 0;
        vif.cb.DATA <= 0;
        vif.cb.META <= 0;
        vif.cb.SOF <= 0;
        vif.cb.EOF <= 0;
        vif.cb.SOF_POS <= 0;
        vif.cb.EOF_POS <= 0;
        vif.cb.SRC_RDY <= 0;
    endfunction

    function void fillEmptyWord();
        if(mode == MODE_ZERO) begin
            vif.cb.DATA <= 0;
            vif.cb.META <= 0;
            vif.cb.SOF <= 0;
            vif.cb.EOF <= 0;
            vif.cb.SOF_POS <= 0;
            vif.cb.EOF_POS <= 0;
            meta = '{default:0};
        end else if(mode == MODE_RANDOM) begin
            DATA_RANDOMIZE1 : assert(std::randomize(data,meta,sof,eof,sof_pos,eof_pos));
            vif.cb.DATA <= { << item {data} };
            vif.cb.META <= { << meta_item {meta} };
            vif.cb.SOF <= sof;
            vif.cb.EOF <= eof;
            vif.cb.SOF_POS <= sof_pos;
            vif.cb.EOF_POS <= eof_pos;
        end else if(mode == MODE_UNDEFINED) begin
            vif.cb.DATA <= 'X;
            vif.cb.META <= 'X;
            vif.cb.SOF <= 'X;
            vif.cb.EOF <= 'X;
            vif.cb.SOF_POS <= 'X;
            vif.cb.EOF_POS <= 'X;
            meta = '{default:'X};
        end
    endfunction

    task moveWord();
        if(src_rdy) begin
            vif.cb.DATA <= { << item {data} };
            vif.cb.META <= { << meta_item {meta} };
            vif.cb.SOF <= sof;
            vif.cb.EOF <= eof;
            vif.cb.SRC_RDY <= src_rdy;
            do
                @(vif.cb);
            while(!vif.cb.DST_RDY);
            vif.cb.SRC_RDY <= 0;
            IDLE_RANDOMIZE1 : assert(randomize());
            if(wordDelayEn)
                repeat(wordDelay)begin
                    fillEmptyWord();
                    vif.cb.SRC_RDY <= 1'b0;
                   @(vif.cb);
                end
        end else begin
           fillEmptyWord();
           vif.cb.SRC_RDY <= 1'b0;
           @(vif.cb);
        end
        sof = 0;
        eof = 0;
        src_rdy = 0;
        offset = 0;
    endtask

    task fillEmptyItems(int size = BLOCK_SIZE);
        repeat(size) begin
            if(mode == MODE_ZERO)
                data[offset] = 0;
            else if(mode == MODE_RANDOM)
                DATA_RANDOMIZE3 : assert(std::randomize(data[offset]));
            else if(mode == MODE_UNDEFINED)
                data[offset] = 'X;
            offset++;
        end
        offset = offset - size;
    endtask

    task moveEmptyBlock();
        fillEmptyItems();
        moveBlock();
    endtask

    task moveBlock();
        offset = offset + BLOCK_SIZE;
        if(offset >= ITEMS)
            moveWord();
    endtask

    task run();
        Transaction transaction;
        MfbTransaction #(ITEM_WIDTH,META_WIDTH) tr;
        int i, j, r, p;
        int transaction_get;
        fillEmptyWord();
        vif.cb.SRC_RDY <= 1'b0;
        @(vif.cb); // initial sync
        sof = 0;
        eof = 0;
        while(enabled) begin
            // move Word if there isnt any transaction or transaction data size
            // is zero
            while((transaction_get = transMbx.try_get(transaction)) == 0 || ($cast(tr, transaction) && tr.data.size() == 0)) begin // wait for transaction

                if (transaction_get != 0) begin
                    moveBlock();
                end else begin
                    moveWord();
                end
                busy = 0;
                if (!enabled) return;
            end
            busy = 1;
            IDLE_RANDOMIZE2 : assert(randomize()); // Inter Frame Gap
            if(ifgEn)
                repeat(ifg)
                    moveEmptyBlock();
            foreach(cbs[i]) cbs[i].pre_tx(transaction, inst); // notify callbacks
            $cast(tr, transaction);
            while(sof[offset / REGION_ITEMS]) // two SOFs not allowed in the same region
                moveEmptyBlock();
            while(((offset + tr.data.size - 1) / REGION_ITEMS < REGIONS) && (eof[(offset + tr.data.size - 1) / REGION_ITEMS])) // two EOFs not allowed in the same region
                moveEmptyBlock();
            if(SOF_CTRL)
                while(((offset / REGION_ITEMS) != tr.sof) || (((offset % REGION_ITEMS) / BLOCK_SIZE) != tr.sof_pos)) // find correct SOF AND find correct SOF position
                    moveEmptyBlock();
            r = offset / REGION_ITEMS; p = offset % REGION_ITEMS; // mark SOF
            sof[r] = 1;
            if (META_ALIGNMENT == 0)
                meta[r] = tr.meta;
            tr.sof = r;
            if(SOF_POS_WIDTH) begin
                vif.cb.SOF_POS[r*SOF_POS_WIDTH +: SOF_POS_WIDTH] <= p / BLOCK_SIZE;
                tr.sof_pos = p / BLOCK_SIZE;
            end
            i = 0;
            while(i < tr.data.size)// transaction written onto bus
                if((tr.data.size-i) > BLOCK_SIZE) begin
                    for(j = 0; j < BLOCK_SIZE; j++, i++)
                        data[offset+j] = tr.data[i];
                    src_rdy = 1;
                    moveBlock();
                end else begin // last block
                    fillEmptyItems();
                    for(j = 0; i < tr.data.size; j++, i++)
                        data[offset+j] = tr.data[i];
                    src_rdy = 1;
                    r = offset / REGION_ITEMS; p = offset % REGION_ITEMS; // mark EOF
                    eof[r] = 1;
                    if (META_ALIGNMENT == 1)
                        meta[r] = tr.meta;
                    if(EOF_POS_WIDTH)
                        vif.cb.EOF_POS[r*EOF_POS_WIDTH +: EOF_POS_WIDTH] <= p + j - 1;
                    foreach(cbs[i]) cbs[i].post_tx(transaction, inst);
                    moveBlock();
                    break;
                end

        end
    endtask

endclass
