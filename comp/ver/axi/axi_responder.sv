/*!
 * \file axi_responder.sv
 * \brief AXI4S Responder
 * \author Martin Spinler <spinler@cesnet.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

class Axi4SResponder #(DATA_WIDTH, USER_WIDTH, ITEM_WIDTH = 8) extends Responder;

    local virtual iAxi4STx#(DATA_WIDTH, USER_WIDTH, ITEM_WIDTH).tb vif;

    // Enables strict TREADY on TVALID dependency.
    //   If set to 1 (or any non-zero value), the AXI responder drives TREADY to 0 by default.
    //   TREADY is driven to 0 after a successful handshake and is asserted one or more clock cycles
    //   (depending on the wordDelay configuration) after TVALID is 1. This limits the throughput
    //   of the AXI responder to <= 50%, however, it tests that the master does not illegally implement
    //   a TVALID on TREADY dependency.
    //   Example waveform (wordDelay = 0):
    //   TVALID   1 1 1 0 1 1 1 1
    //   TREADY   1 0 1 0 0 1 0 1
    bit treadyDepEn = 0;

    rand bit wordDelayEn;
    int wordDelayEnable_wt = 1;
    int wordDelayDisable_wt = 3;
    rand integer wordDelay;
    int wordDelayLow = 0;
    int wordDelayHigh = 3;

    constraint cDelays{
        wordDelayEn dist {1'b1 := wordDelayEnable_wt, 1'b0 := wordDelayDisable_wt};
        wordDelay inside { [wordDelayLow:wordDelayHigh] };
    }

    function new(string i, virtual iAxi4STx#(DATA_WIDTH, USER_WIDTH, ITEM_WIDTH).tb v);
        super.new(i);
        vif = v;
        vif.cb.TREADY <= 0;
    endfunction

    virtual task run();
        vif.cb.TREADY <= 0;
        @(vif.cb);
        while(enabled) begin
            IDLE_RANDOMIZE : assert(randomize());
            if (treadyDepEn) begin
                // enter TREADY at zero after handshake for 1 clock cycle (may be extended by wordDelay)
                vif.cb.TREADY<= 0;
                @(vif.cb iff vif.cb.TVALID == 1'b1);
            end
            if(wordDelayEn)
                // enter TREADY at zero for wordDelay clock cycles
                repeat(wordDelay) begin
                    vif.cb.TREADY<= 0;
                    @(vif.cb);
                end
            vif.cb.TREADY <= 1;
            @(vif.cb);
        end
        vif.cb.TREADY <= 0;
    endtask

endclass
