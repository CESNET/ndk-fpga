/*!
 * \file       mi32_responder.sv
 * \brief      Responder for MI interface
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

class Mi32Responder extends Responder;

	local virtual iMi32.responder vif;

	rand bit delayEn;
	int delayEnable_wt = 1;
	int delayDisable_wt = 3;

	rand integer delay;
	int delayLow = 0;
	int delayHigh = 3;

	constraint cDelays{
		delayEn dist {
			1'b1 := delayEnable_wt,
			1'b0 := delayDisable_wt
		};
		delay inside {[delayLow:delayHigh]};
	}

	function new(string i, virtual iMi32.responder v);
		super.new(i);
		vif = v;
		vif.ARDY <= 0;
		vif.DRDY <= 0;
	endfunction

	task wordRandomWait();
		assert(randomize());

		if (delayEn) begin
			repeat (delay) begin
				@(posedge vif.CLK);
			end
		end
	endtask

	virtual task run();
		/* TODO: connect to generator */
		int counter = 32'h0c080400;

		while (enabled) begin
			wordRandomWait();

			if (vif.WR == 1) begin
				vif.ARDY <= 1;
			end else if (vif.RD == 1) begin
				vif.ARDY <= 1;
				vif.DRDY <= 1;
				vif.DRD <= counter;
				counter += 32'h01010101;
			end else begin
				vif.ARDY <= 0;
				vif.DRDY <= 0;
			end
			@(posedge vif.CLK);
			vif.ARDY <= 0;
			vif.DRDY <= 0;
		end
	endtask

endclass
