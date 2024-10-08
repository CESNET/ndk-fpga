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
            if(wordDelayEn)
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
