/*!
 * \file       mi32_monitor_new.sv
 * \brief      MI32 monitor - new version
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

class Mi32Monitor extends Monitor;
	virtual iMi32.monitor mi;

	tTransMbx transMbx;
	Mi32Transaction readRequests[$];

	function new (string inst, virtual iMi32.monitor mi);
		super.new(inst);

		this.mi = mi;
		transMbx = new();
	endfunction

	task handleDRDY();
		Transaction transaction;
		Mi32Transaction tr;

		while (enabled) begin
			transMbx.get(transaction);
			$cast(tr, transaction);
			if (mi.monitor_cb.DRDY == 1) begin
				tr.data = mi.monitor_cb.DRD;

				$cast(transaction, tr);

				foreach (cbs[i])
					cbs[i].post_rx(transaction, inst);
			end else begin
				@(mi.monitor_cb);
			end
		end
	endtask

	virtual task run();
		Transaction transaction;
		Mi32Transaction tr;

		fork
			handleDRDY();
		join_none;

		while (enabled) begin
			if (mi.monitor_cb.WR == 1 && mi.monitor_cb.ARDY == 1) begin
				tr = new;
				$cast(transaction, tr);
				foreach (cbs[i])
					cbs[i].pre_rx(transaction, inst);

				tr.address = mi.monitor_cb.ADDR;
				tr.data    = mi.monitor_cb.DWR;
				tr.be      = mi.monitor_cb.BE;
				tr.rw      = 1;
				foreach (cbs[i])
					cbs[i].post_rx(transaction, inst);
			end
			if (mi.monitor_cb.RD == 1 && mi.monitor_cb.ARDY == 1) begin
				tr = new;
				$cast(transaction, tr);
				foreach (cbs[i])
					cbs[i].pre_rx(transaction, inst);

				tr.address = mi.monitor_cb.ADDR;
				tr.be      = mi.monitor_cb.BE;
				tr.rw      = 0;
				transMbx.put(tr);
			end

			@(mi.monitor_cb);
		end
	 endtask

endclass

