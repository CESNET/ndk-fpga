/*!
 * \file test.sv
 * \brief Test Cases
 * \author Daniel Kriz <xkrizd01@vutbr.cz>
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
import sv_mvb_pkg::*;
import test_pkg::*;

program TEST (
    input logic CLK,
    output logic RESET,
    input logic[CNT_WIDTH-1 : 0] FRAME_COUNTER,
    iMfbRx.tb RX,
    iMfbTx.tb TX,
    iMfbTx.monitor MONITOR
);

    MfbTransaction #(ITEM_WIDTH,CNT_WIDTH) blueprint;
    Generator generator;
    MfbDriver    #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,0,CNT_WIDTH,0) driver;
    MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,CNT_WIDTH,0) responder;
    MfbMonitor   #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,CNT_WIDTH,0) monitor;
    Scoreboard scoreboard;

    task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
        generator = new("Generator", 0);
        blueprint = new;
        blueprint.frameSizeMax = packet_size_max;
        blueprint.frameSizeMin = packet_size_min;
        generator.blueprint = blueprint;
    endtask

    task createEnvironment();
        driver  = new("Driver", generator.transMbx, RX);
        monitor = new("MFB Monitor", MONITOR);
        responder = new("Responder", TX);

        scoreboard = new;
        driver.setCallbacks(scoreboard.driverCbs);
        monitor.setCallbacks(scoreboard.monitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task checkCounter();
        if(AUTO_RESET == 1) begin
            if((TRANSACTION_COUNT%(CNT_WIDTH_MAX)) == FRAME_COUNTER) begin
                $write("Counter is OK \n");
            end else begin
                $write("Value of counter: %d\n", FRAME_COUNTER);
                $write("Expected value: %d\n", TRANSACTION_COUNT);
                $write("Counter is not OK \n");
                $stop();
            end;
        end;
        if(AUTO_RESET == 0) begin
            if((TRANSACTION_COUNT >= CNT_WIDTH_MAX-1) && (FRAME_COUNTER == CNT_WIDTH_MAX-1)) begin
                $write("Counter is OK \n");
            end

            else if ((TRANSACTION_COUNT <= CNT_WIDTH_MAX-1) && (FRAME_COUNTER == TRANSACTION_COUNT)) begin
                $write("Counter is OK \n");
            end

            else begin

                if(TRANSACTION_COUNT >= CNT_WIDTH_MAX-1) begin
                    $write("Value of counter: %d\n", FRAME_COUNTER);
                    $write("Expected value: %d\n", CNT_WIDTH_MAX-1);
                    $write("Counter is not OK \n");
                    $stop();
                end;

                if(TRANSACTION_COUNT <= CNT_WIDTH_MAX-1) begin
                    $write("Value of counter: %d\n", FRAME_COUNTER);
                    $write("Expected value: %d\n", TRANSACTION_COUNT);
                    $write("Counter is not OK \n");
                    $stop();
                end;

            end;
        end;
    endtask

    task enableTestEnvironment();
        driver.setEnabled();
        monitor.setEnabled();
        responder.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!driver.busy);
        do begin
            wait(!(monitor.busy));
            fork : StayIdleWait
                wait(monitor.busy) disable StayIdleWait;
                #(100*CLK_PERIOD) disable StayIdleWait;
            join
        end while(monitor.busy);
        driver.setDisabled();
        monitor.setDisabled();
        responder.setDisabled();
    endtask

    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        enableTestEnvironment();
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        disableTestEnvironment();
        checkCounter();
        scoreboard.display();

    endtask

    initial begin
        resetDesign();
        createGeneratorEnvironment(FRAME_SIZE_MAX, FRAME_SIZE_MIN);
        createEnvironment();
        test1();
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
