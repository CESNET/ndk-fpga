/*!
 * \file mfb_responder.sv
 * \brief Multi-Frame Bus responder
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



class MfbResponder #(REGIONS = 4, REGION_SIZE = 8, BLOCK_SIZE = 8, ITEM_WIDTH = 8, META_WIDTH = 1, META_ALIGNMENT = 0);

    localparam BLOCKS = REGIONS * REGION_SIZE;


    string inst;
    bit enabled;
    local virtual iMfbTx#(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,META_WIDTH).tb vif;

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


    function new(string i, virtual iMfbTx#(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,META_WIDTH).tb v);
        enabled = 0;
        vif = v;
        inst = i;
        vif.cb.DST_RDY <= 0;
    endfunction

    task setEnabled();
        enabled = 1;
        fork
            run();
        join_none;
    endtask

    task setDisabled();
        enabled = 0;
    endtask

    task run();
        vif.cb.DST_RDY <= 0;
        @(vif.cb);
        while(enabled) begin
            IDLE_RANDOMIZE : assert(randomize());
            if(wordDelayEn)
                repeat(wordDelay) begin
                    vif.cb.DST_RDY <= 0;
                    @(vif.cb);
                end
            vif.cb.DST_RDY <= 1;
            @(vif.cb);
        end
        vif.cb.DST_RDY <= 0;
    endtask

endclass
