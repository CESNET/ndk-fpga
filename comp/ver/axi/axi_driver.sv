/*!
 * \file       axi_driver.sv
 * \brief      AXI4S Driver
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

class Axi4SDriver #(DATA_WIDTH, USER_WIDTH, ITEM_WIDTH = 8) extends Driver;

	virtual iAxi4SRx#(DATA_WIDTH, USER_WIDTH, ITEM_WIDTH).tb vif;

	parameter WORD_ITEMS = DATA_WIDTH / ITEM_WIDTH;
	parameter ITEM_BYTES = ITEM_WIDTH / 8;

	rand bit enTxDelay;
	int txDelayEn_wt      = 1;
	int txDelayDisable_wt = 3;

	rand int txDelay;
	int txDelayLow  = 0;
	int txDelayHigh = 3;

	constraint cDelaysPositions {
		enTxDelay dist {
				1'b1 := txDelayEn_wt,
				1'b0 := txDelayDisable_wt
		};

		txDelay inside {[txDelayLow:txDelayHigh]};
	}

	function new(string inst, tTransMbx transMbx, virtual iAxi4SRx#(DATA_WIDTH, USER_WIDTH, ITEM_WIDTH).tb v);
		super.new(inst, transMbx);
		this.vif = v;

		this.vif.cb.TVALID	 <= 0;
	endfunction

	task sendTransaction(AxiTransaction transaction);
		Transaction tr;
		$cast(tr, transaction);

		busy = 1;

		foreach (cbs[i])
			cbs[i].pre_tx(tr, inst);

		sendFrame(transaction);

		foreach (cbs[i])
			cbs[i].post_tx(tr, inst);

		busy = 0;
	endtask

	task run();
		AxiTransaction transaction;
		Transaction to;
		time before_get;

		@(vif.cb);

		while (enabled) begin
			assert(randomize());
			before_get = $time;
			transMbx.get(to);
			if ($time != before_get)
				@(vif.cb);
			$cast(transaction,to);
			sendTransaction(transaction);
		end
	endtask

	task waitForWordAccept();
		while (!vif.cb.TREADY) begin
			@(vif.cb);
		end;
	endtask

	task wordRandomWait();
		assert(randomize());

		if (enTxDelay) begin
			repeat (txDelay) begin
				@(vif.cb);
			end
		end;
	endtask

	task frameRandomWait();
		assert(randomize());

		if (enTxDelay) begin
			repeat (txDelay) begin
				@(vif.cb);
			end
		end;
	endtask

	virtual task validateWord(int finished);
		if (finished)
			vif.cb.TLAST <= 1;
		vif.cb.TVALID <= 1;
	endtask

	virtual task invalidateWord();
		vif.cb.TVALID <= 0;
		vif.cb.TLAST <= 0;
	endtask

	virtual task invalidateWordData();
		logic[DATA_WIDTH-1:0] data = 'x;
		logic[WORD_ITEMS-1:0] keep= 'x;

		vif.cb.TDATA <= data;
		vif.cb.TKEEP <= keep;
	endtask

	virtual task exposeWordData(AxiTransaction tr, int cycle, inout finished);
		logic[DATA_WIDTH-1:0] data = 'x;
		logic[WORD_ITEMS-1:0] keep = '0;
		int j;

		for (j = 0; j < WORD_ITEMS * ITEM_BYTES && j + WORD_ITEMS * cycle < tr.data.size; j += ITEM_BYTES) begin
			{<<8{data[j / ITEM_BYTES * ITEM_WIDTH +: ITEM_WIDTH]}} = tr.data[j + ITEM_BYTES * WORD_ITEMS * cycle +: ITEM_BYTES];
			keep[j / ITEM_BYTES] = 1;
		end

		if (j + ITEM_BYTES * WORD_ITEMS * cycle >= tr.data.size)
			finished = 1;

		vif.cb.TDATA <= data;
		vif.cb.TKEEP <= keep;
	endtask

	virtual task sendWord(AxiTransaction tr, int cycle, inout finished);
		wordRandomWait();
		exposeWordData(tr, cycle, finished);
		validateWord(finished);
		@(vif.cb);
		waitForWordAccept();
		invalidateWord();
		invalidateWordData();
	endtask

	virtual task sendFrame(AxiTransaction tr);
		int cycle = 0;
		int finished = 0;

		do begin
			sendWord(tr, cycle, finished);
			cycle++;
		end while (finished == 0);
	endtask

endclass

