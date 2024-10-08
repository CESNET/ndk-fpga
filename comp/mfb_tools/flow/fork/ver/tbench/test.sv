/*!
 * \file test.sv
 * \brief Test Cases
 * \author Daniel Kříž <xkrizd01@vutbr.cz>
 * \date 2020
 */
 /*
 * Copyright (C) 2020 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import sv_common_pkg::*;
import sv_mfb_pkg::*;
import test_pkg::*;

program TEST (
    input logic CLK,
    output logic RESET,
    iMfbRx RX,
    iMfbTx TX[OUTPUT_PORTS]
);

    MfbTransaction #(ITEM_WIDTH,META_WIDTH) blueprint;
    Generator generator;
    MfbDriver #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,0,META_WIDTH) driver;
    MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,META_WIDTH) responder[OUTPUT_PORTS];
    MfbMonitor #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,META_WIDTH) monitor[OUTPUT_PORTS];
    Scoreboard scoreboard;
    virtual iMfbTx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,META_WIDTH) vTX[OUTPUT_PORTS];

    task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
        generator = new("Generator", 0);
        blueprint = new;
        blueprint.frameSizeMax = packet_size_max;
        blueprint.frameSizeMin = packet_size_min;
        generator.blueprint = blueprint;
    endtask

    task createEnvironment();
        scoreboard = new;
        vTX = TX;
        driver  = new("Driver", generator.transMbx, RX);
        driver.setCallbacks(scoreboard.driverCbs);
        foreach(monitor[i]) begin
            string name;
            name = $sformatf( "Monitor %0d ", i);
            monitor[i] = new(name, vTX[i]);
            monitor[i].setCallbacks(scoreboard.monitorCbs[i]);
        end
        foreach(responder[i]) begin
            responder[i] = new("Responder", vTX[i]);
            if(!USE_DST_RDY) begin
                responder[i].wordDelayEnable_wt = 0;
                responder[i].wordDelayDisable_wt = 1;
            end
        end
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        driver.setEnabled();
        foreach(responder[i]) begin
            responder[i].setEnabled();
        end
    endtask

    task disableTestEnvironment();
        wait(!driver.busy);
        do begin
            wait(!monitor[0].busy);
            fork : StayIdleWait
                wait(monitor[0].busy) disable StayIdleWait;
                #(100*CLK_PERIOD) disable StayIdleWait;
            join
        end while(monitor[0].busy);
        driver.setDisabled();
        foreach(monitor[i]) begin
            monitor[i].setDisabled();
        end
        foreach(responder[i]) begin
            responder[i].setDisabled();
        end
    endtask

    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        foreach(monitor[i]) begin
            monitor[i].setEnabled();
        end
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        disableTestEnvironment();
        scoreboard.display();
    endtask

    initial begin
        createGeneratorEnvironment(FRAME_SIZE_MAX, FRAME_SIZE_MIN);
        createEnvironment();
        enableTestEnvironment();
        resetDesign();
        test1();
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
