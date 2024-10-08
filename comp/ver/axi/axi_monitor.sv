/*!
 * \file       axi_monitor.sv
 * \brief      AXI4S Monitor
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

class Axi4SMonitor #(int DATA_WIDTH = 512, int USER_WIDTH = 1, int ITEM_WIDTH = 8, type tAxiTransaction = AxiTransaction #(ITEM_WIDTH)) extends Monitor;

	typedef bit [ITEM_WIDTH-1:0] item;

	virtual iAxi4STx#(DATA_WIDTH, USER_WIDTH, ITEM_WIDTH).monitor vif;

	function new(string i, virtual iAxi4STx#(DATA_WIDTH, USER_WIDTH, ITEM_WIDTH).monitor v);
		super.new(i);
		vif = v;
	endfunction

	virtual task processUser(AxiTransaction tr, int cycle);
	endtask

	virtual task run();
		int i;
		int inframe = 0;
		int cycle;
		tAxiTransaction tTr;
		Transaction transaction;
		AxiTransaction #(ITEM_WIDTH) tr;
		bit [ITEM_WIDTH-1:0] buffer[$], data[DATA_WIDTH / ITEM_WIDTH];

		while (enabled) begin
			do begin
				 @(vif.monitor_cb);
				 busy = vif.monitor_cb.TVALID;
			end while (enabled && !(vif.monitor_cb.TVALID && vif.monitor_cb.TREADY));

			if (!enabled)
				break;

			if (!inframe) begin
				inframe = 1;
				cycle = 0;
				tTr = new();
				$cast(tr, tTr);
				$cast(transaction, tr);
				foreach (cbs[i])
					cbs[i].pre_rx(transaction, inst);
			end

			data = {<<item{vif.monitor_cb.TDATA}};
			for (i = 0; i < DATA_WIDTH / ITEM_WIDTH; i++)
				if (vif.monitor_cb.TKEEP[i])
					buffer = {buffer, data[i]};

			processUser(tr, cycle);

			if (vif.monitor_cb.TLAST) begin
				tr.data = buffer;
				foreach (cbs[i])
					cbs[i].post_rx(transaction, inst);
				buffer = {};
				inframe = 0;
			end
			cycle++;
		end
	endtask

endclass
