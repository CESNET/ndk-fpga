/*!
 * \file       axi4s_rq_agent.sv
 * \brief      agent for AXI_RQ PCIe endpoint interface
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

class Axi4S_RQ_agent #(DATA_WIDTH = 512, USER_WIDTH = 137, ITEM_WIDTH_IN = 8, ST_COUNT = 4) extends Monitor;

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

	protected virtual iAxi4STx#(DATA_WIDTH, USER_WIDTH, ITEM_WIDTH_IN) vif;

	typedef bit [ITEM_WIDTH-1 : 0] item;

	int garbageSize = 0;
	int old_inframe = 0;
	int inframe = 0;

	function new(string i, virtual iAxi4STx#(DATA_WIDTH, USER_WIDTH, ITEM_WIDTH_IN) v);
		super.new(i);
		vif = v;
		vif.cb.TREADY <= 1;
	endfunction

	virtual task setEnabled();
		enabled = 1;
		fork
			run();
		join_none;
	endtask

	function int hasSOF();
      if (USER_WIDTH==137) // ULTRASCALE
         return vif.cb.TUSER[21:20];
      else begin // 7SERIES
         if (!inframe)
            return vif.cb.TVALID;
         else
            return 0;
      end
	endfunction

	function int hasEOF();
      if (USER_WIDTH==137) // ULTRASCALE
         return vif.cb.TUSER[27:26];
      else begin // 7SERIES
         return vif.cb.TLAST;
      end
	endfunction

    function logic [3:0] fbe(int unsigned index);
        if(USER_WIDTH== 137) begin
            return vif.cb.TUSER[(index+1)*4-1 -: 4];
        end else if (USER_WIDTH == 60) begin
            return vif.cb.TUSER[3:0];
        end else begin
            $write("NOT SUPPORTED AXI USER_WIDTH\n");
            $stop();
        end
    endfunction

    function logic [3:0] lbe(int unsigned index);
        if(USER_WIDTH== 137) begin
            return vif.cb.TUSER[(index+1)*4+7 -: 4];
        end else if (USER_WIDTH == 60) begin
            return vif.cb.TUSER[7:4];
        end else begin
            $write("NOT SUPPORTED AXI USER_WIDTH\n");
            $stop();
        end
    endfunction

	function int sofPos(int index);
      if (USER_WIDTH==137) // ULTRASCALE
         return index;
      else begin // 7SERIES
         return 0;
      end
	endfunction

	function int eofPos(int index);
      int pos = 0;
      int j = 0;
      if (USER_WIDTH==137) begin // ULTRASCALE
         if ((vif.cb.TUSER[26] && vif.cb.TUSER[31:31] == index))
            return vif.cb.TUSER[30:28];
         if ((vif.cb.TUSER[27] && vif.cb.TUSER[35:35] == index))
            return vif.cb.TUSER[34:32];
      end else begin // 7SERIES
         for (j = 0; j < REGION_ITEMS; j++) begin
            if (vif.cb.TKEEP[j]==1'b0)
               break;
            pos = j;
         end
         return pos;
      end
		return -1;
	endfunction

	function int isSOF(int index);
      if (USER_WIDTH==137) begin // ULTRASCALE
         if ((vif.cb.TUSER[20] && vif.cb.TUSER[23:23] == index) ||
               (vif.cb.TUSER[21] && vif.cb.TUSER[25:25] == index))
            return 1;
      end else begin // 7SERIES
         if (!old_inframe)
            return vif.cb.TVALID;
      end
		return 0;
	endfunction

	function int isEOF(int index);
      if (USER_WIDTH==137) begin // ULTRASCALE
         if ((vif.cb.TUSER[26] && vif.cb.TUSER[31:31] == index) ||
               (vif.cb.TUSER[27] && vif.cb.TUSER[35:35] == index))
            return 1;
      end else begin // 7SERIES
         return hasEOF(); // only 1 region
      end
		return 0;
	endfunction

	virtual task run();
		Transaction transaction;
		AxiTransaction #(ITEM_WIDTH) tr;
		bit [ITEM_WIDTH-1 : 0] buffer[$], data[ITEMS];
		int i, j, start, offset, later, late, data_id;
		buffer = {};
		inframe = 0;
		offset = 0;
		data_id = 0;

		while (enabled) begin
			do begin
				@(vif.monitor_cb);
				busy = inframe || vif.monitor_cb.TVALID;
				if (inframe && !vif.monitor_cb.TVALID) begin
					$write("@%0t - %s: Error in AXI RQ protocol! Source not ready inside frame.\n", $time, inst);
               $stop();
            end
	    	end while (enabled && !(vif.monitor_cb.TVALID && vif.monitor_cb.TREADY));

         //$write("--99--\n");
         //$write("@%0t\n", $time);
         //$write("user: 0x%x\n",vif.cb.TDATA);
         //$write("user: 0x%x\n",vif.cb.TUSER);
         //$write("old_inframe: %d\n",old_inframe);
         //$write("inframe: %d\n",inframe);
         //$write("start: %d\n",start);
         //$write("offset: %d\n",offset);
         //$write("hasSOF: %d\n",hasSOF());
         //$write("hasEOF: %d\n",hasEOF());


			if (!enabled)
				break;

			if (start > garbageSize) begin // clean old data from buffer
				buffer = {buffer[start : $]};
				offset = offset - start;
				start = 0;
			end

            data = { << item {vif.monitor_cb.TDATA} };
			buffer = {buffer, data};

			if (!hasSOF() && !hasEOF()) begin // nothing important in this word
				if(!inframe) begin
					$write("@%0t - %s: Error in MFB protocol! Valid data outside frame.\n", $time, inst);
               $stop();
            end
				offset = offset + ITEMS;
			end else begin // some SOF or EOF => process them
				for (j = 0; j < REGIONS; j++, offset = offset+REGION_ITEMS) begin
               //$write("--01--\n");
               //$write("j: %d\n",j);
               //$write("old_inframe: %d\n",old_inframe);
               //$write("inframe: %d\n",inframe);
               //$write("offset: %d\n",offset);
               //$write("isSOF(j): %d\n",isSOF(j));
               //$write("isEOF(j): %d\n",isEOF(j));
               //$write("sofPos(j): %d\n",sofPos(j));
               //$write("eofPos(j): %d\n",eofPos(j));
					if (SOF_POS_WIDTH && isSOF(j) && isEOF(j)) // SOF and EOF in the same region
							later = 0;
							//later = sofPos(j) > eofPos(j); // Never happens
					else
							later = 0; // EOF after SOF in the region
					late = 0;
               //$write("--02--\n");
               //$write("later: %d\n",later);
               //$write("late: %d\n",late);
					do begin
                  if (isSOF(j) && !later) begin // SOF processing
                     if (inframe) begin
                        $write("@%0t - %s: Error in MFB protocol! SOF detected inside frame in region #%1d.\n", $time, inst, j);
                        $stop();
                     end else begin
                        inframe = 1;
                        tr = new;
                        tr.data_id = data_id;
                        data_id = data_id + 1;
                        $cast(transaction, tr);
                        foreach(cbs[i]) cbs[i].pre_rx(transaction, inst);
                        if(SOF_POS_WIDTH) begin
                              start = offset + sofPos(j) * BLOCK_SIZE;
                        end else begin
                              start = offset;
                        end
                        tr.fbe = fbe(j);
                        tr.lbe = lbe(j);
                        //$write("--03--\n");
                        //$write("new start: %d\n",start);
                     end
                  end
                  if (isEOF(j) & !late) begin // EOF processing
                     if (inframe) begin
                        if(EOF_POS_WIDTH) begin
                              //$write("--04--\n");
                              //$write("from: %d\n",start);
                              //$write("to: %d\n",offset+ (eofPos(j) + 1) * 4 - 1);
                              tr.data = buffer[start : offset + (eofPos(j) + 1) * 4 - 1];
                        end else begin
                              tr.data = buffer[start : offset];
                        end
                        foreach (cbs[i]) cbs[i].post_rx(transaction, inst);
                            inframe = 0;
                     end else begin
                        $write("@%0t - %s: Error in MFB protocol! EOF detected outside frame in region #%1d.\n", $time, inst, i);
                        $stop();
                     end
                  end
                  late = later; later = 0;
					end while (late);
				end
            old_inframe = inframe;
			end
		end
	endtask

endclass
