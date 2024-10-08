/*!
 * \file       axi4s_rc_agent.sv
 * \brief      agent for AXI_RC PCIe endpoint interface
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

class Axi4S_RC_agent #(DATA_WIDTH = 512, USER_WIDTH = 161, ITEM_WIDTH_IN = 8, ST_COUNT = 4) extends Driver;

    localparam REGIONS = ST_COUNT;
    localparam REGION_SIZE = 1;
    localparam ITEM_WIDTH = 8;
	 localparam BLOCK_SIZE = DATA_WIDTH/REGIONS/ITEM_WIDTH;

    protected int sof_pos[REGIONS];
    protected int eof_pos[REGIONS];

    localparam ITEMS = REGIONS * REGION_SIZE * BLOCK_SIZE;
    localparam REGION_ITEMS = REGION_SIZE * BLOCK_SIZE;
    localparam WORD_BLOCKS = REGIONS * REGION_SIZE;
    localparam SOF_POS_WIDTH = $clog2(REGION_SIZE);
    localparam EOF_POS_WIDTH = $clog2(REGION_SIZE * BLOCK_SIZE);
    typedef bit [ITEM_WIDTH-1 : 0] item;
    typedef bit [3:0] item_valid;

    protected virtual iAxi4SRx#(DATA_WIDTH, USER_WIDTH, ITEM_WIDTH_IN).tb vif;
    protected int offset = 0;
    protected item data[ITEMS];
    protected item_valid  valid[ITEMS/4];
    protected bit [REGIONS-1 : 0] sof;
    protected bit [REGIONS-1 : 0] eof;
    protected bit src_rdy;

    rand bit wordDelayEn;
    int wordDelayEnable_wt = 0;
    int wordDelayDisable_wt = 1;
    rand integer wordDelay;
    int wordDelayLow = 0;
    int wordDelayHigh = 3;

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

    function new(string i, tTransMbx t, virtual iAxi4SRx#(DATA_WIDTH, USER_WIDTH, ITEM_WIDTH_IN).tb v);
        super.new(i, t);
        vif = v;
        offset = 0;
        sof = 0;
        eof = 0;
        src_rdy = 0;
        vif.cb.TVALID <= 0;
        vif.cb.TDATA <= 0;
    endfunction

    task assignUser();
        int a1 = 0;
        int a2 = 0;
        int st = 0;

        bit [ST_COUNT-1 : 0] is_sop = {ST_COUNT{1'b0}};
        bit [ST_COUNT-1 : 0] is_eop = {ST_COUNT{1'b0}};
        bit [1:0] sop_pos[ST_COUNT] = '{ST_COUNT {2'b0}};
        bit [3:0] eop_pos[ST_COUNT] = '{ST_COUNT {2'b0}};

        for(st = 0; st < ST_COUNT; st++) begin
           //$write("st: %d\n",st);
           if(sof[st] == 1) begin
              //$write("sof\n");
              is_sop[a1] = 1;
              sop_pos[a1] = st;
              a1++;
           end
           if(eof[st] == 1) begin
              //$write("eof\n");
              is_eop[a2] = 1;
              if (USER_WIDTH==161) begin // Ultrascale
                 eop_pos[a2][3:2] = st;
                 eop_pos[a2][1:0] = eof_pos[st];
              end else begin // 7Series
                 eop_pos[a2][2:2] = st;
                 eop_pos[a2][1:0] = eof_pos[st];
              end
              a2++;
           end
        end
        //$write("sof: %d\n",sof);
        //$write("eof: %d\n",eof);
        //$write("sof_pos: %p\n",sof_pos);
        //$write("eof_pos: %p\n",eof_pos);
        //$write("is_sop: %d\n",is_sop);
        //$write("is_eop: %d\n",is_eop);
        //$write("sop_pos: %p\n",sop_pos);
        //$write("eop_pos: %p\n",eop_pos);

        vif.cb.TUSER <= 0;
        if (USER_WIDTH==161) begin // Ultrascale
           vif.cb.TUSER[63+ST_COUNT:64] <= is_sop;
           vif.cb.TUSER[75+ST_COUNT:76] <= is_eop;

           vif.cb.TUSER[69:68] <= sop_pos[0];
           vif.cb.TUSER[71:70] <= sop_pos[1];
           vif.cb.TUSER[73:72] <= sop_pos[2];
           vif.cb.TUSER[75:74] <= sop_pos[3];

           vif.cb.TUSER[83:80] <= eop_pos[0];
           vif.cb.TUSER[87:84] <= eop_pos[1];
           vif.cb.TUSER[91:88] <= eop_pos[2];
           vif.cb.TUSER[95:92] <= eop_pos[3];
        end else begin // 7Series
           vif.cb.TUSER[31+ST_COUNT:32] <= is_sop;
           vif.cb.TUSER[34] <= is_eop[0];
           vif.cb.TUSER[38] <= is_eop[1];

           vif.cb.TUSER[37:35] <= eop_pos[0];
           vif.cb.TUSER[41:39] <= eop_pos[1];
        end
    endtask

/*    task assignUserSop();
        int a1 = 0;
        int st = 0;

        bit [ST_COUNT-1 : 0] is_sop = {ST_COUNT{1'b0}};
        bit [1:0] sop_pos[ST_COUNT] = {0};
        bit [3:0] eop_pos[ST_COUNT] = {0};

        for(st = 0; st < ST_COUNT; st++) begin
           if(sof[st] == 1) begin
              is_sop[a1] = 1;
              sop_pos[a1] = st;//{<<{st}};
              a1++;
           end
           if(eof[st] == 1) begin
              is_eop[a2] = 1;
              eop_pos[a2] = st;//{<<{st}};
              a2++;
           end
        end

        vif.cb.TUSER <= 0;
        vif.cb.TUSER[63+ST_COUNT:64] <= is_sop;
        vif.cb.TUSER[75+ST_COUNT:76] <= is_eop;

        vif.cb.TUSER[69:68] <= sop_pos[0];
        vif.cb.TUSER[71:70] <= sop_pos[1];
        vif.cb.TUSER[73:72] <= sop_pos[2];
        vif.cb.TUSER[75:74] <= sop_pos[3];
    endtask
*/

    task moveWord();
        assignUser();
        vif.cb.TDATA <= { << item {data} };
        if (USER_WIDTH == 161) begin
            vif.cb.TUSER[63:0] <= { << item_valid {valid} };
        end else begin
            vif.cb.TUSER[31:0] <= { << item_valid {valid} };
        end
        valid = '{ITEMS/4{4'h0}};
        vif.cb.TVALID <= src_rdy;
        // TLAST is no more valid with ST_COUNT > 1
        //vif.cb.TLAST <= eof;

        if(src_rdy) begin
            do
                @(vif.cb);
            while(!vif.cb.TREADY);
            vif.cb.TVALID <= 0;
            IDLE_RANDOMIZE : assert(randomize());
            if(wordDelayEn)
                repeat(wordDelay)
                    @(vif.cb);
        end else
            @(vif.cb);
        sof = 0;
        eof = 0;
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
        AxiTransaction #(ITEM_WIDTH) tr;
        item_valid tr_valid[];
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
            while(sof[offset / REGION_ITEMS]) // two SOFs not allowed in the same region
                moveBlock();
            while(eof[(offset + tr.data.size - 1) / REGION_ITEMS]) // two EOFs not allowed in the same region
                moveBlock();
/*            if(SOF_CTRL)
                while(((offset / REGION_ITEMS) != tr.sof) || (((offset % REGION_ITEMS) / BLOCK_SIZE) != tr.sof_pos)) // find correct SOF AND find correct SOF position
                    moveBlock();*/

            r = offset / REGION_ITEMS; p = offset % REGION_ITEMS; // mark SOF
            if (USER_WIDTH!=161) begin // 7Series
               if (r!=0 && sof[0]==0 && eof[0]==0) begin
                  // There must not be a gap in region 0 (according to specification)
                  offset -= REGION_ITEMS;
                  r = 0;
               end
            end
            sof[r] = 1;
            sof_pos[r] = p / BLOCK_SIZE;
            assignUser();
/*            if(SOF_POS_WIDTH)
                vif.cb.SOF_POS[r*SOF_POS_WIDTH +: SOF_POS_WIDTH] <= p / BLOCK_SIZE;*/
            i = 0;
            //$write("---00--\n");
            //$write("@%0t\n", $time);
            //$write("REGIONS: %d\n",REGIONS);
            //$write("REGION_SIZE: %d\n",REGION_SIZE);
	         //$write("BLOCK_SIZE: %d\n",BLOCK_SIZE);
            //$write("ITEM_WIDTH: %d\n",ITEM_WIDTH);
            //$write("ITEMS: %d\n",ITEMS);
            //$write("REGION_ITEMS: %d\n",REGION_ITEMS);
            //$write("WORD_BLOCKS: %d\n",WORD_BLOCKS);
            //$write("SOF_POS_WIDTH: %d\n",SOF_POS_WIDTH);
            //$write("EOF_POS_WIDTH: %d\n",EOF_POS_WIDTH);
            //$write("offset: %d\n",offset);
            //$write("r: %d\n",r);
            //$write("p: %d\n",p);
            //$write("data size: %d\n",tr.data.size);
            //$write("data: %p\n",tr.data);
            tr_valid = new [(tr.data.size()+3)/4];
            for (int unsigned it = 0; it < tr_valid.size(); it++) begin
                tr_valid[it] = 4'hf;
            end
            tr_valid[0] = 4'h0;
            tr_valid[1] = 4'h0;
            tr_valid[2] = 4'h0;
            tr_valid[tr_valid.size()-1] = tr.lbe; //lbe can be fbe
            tr_valid[3] = tr.fbe;

            while(i < tr.data.size()) begin// transaction written onto bus
                int unsigned it_end  = BLOCK_SIZE < (tr.data.size() -i) ? BLOCK_SIZE : (tr.data.size() -i);
                int unsigned it;
                for (it = 0; it < it_end; it++) begin
                    data[offset + it]   = tr.data[i];
                    valid[(offset + it)/4]  = tr_valid[i/4];
                    i++;
                end

                src_rdy = 1;
                if(i >= tr.data.size()) begin
                    r = offset / REGION_ITEMS;
                    p = offset % REGION_ITEMS; // mark EOF
                     //$write("---03--\n");
                     //$write("offset: %d\n",offset);
                     //$write("r: %d\n",r);
                     //$write("j: %d\n",j);
                    eof[r] = 1;
                    eof_pos[r] = p + it/4 - 1;
                    assignUser();
                end
                moveBlock();
            end
            //cbs transaction
            foreach(cbs[i]) cbs[i].post_tx(transaction, inst);
            //$write("---04--\n");
        end
    endtask

endclass
