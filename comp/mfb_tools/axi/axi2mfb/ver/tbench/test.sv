/* test.sv: test
 * Copyright (C) 2024 BrnoLogic, Ltd.
 * Author(s): Radek Hajek <hajek@brnologic.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import sv_common_pkg::*;
import sv_mfb_pkg::*;
import sv_axi_pkg::*;
import test_pkg::*;

program TEST (
    input logic CLK,
    output logic RESET,
    iAxi4SRx.tb RX,
    iMfbTx.tb TX,
    iMfbTx.monitor MONITOR
);

    AxiTransaction #(ITEM_WIDTH) blueprint;
    Generator generator;
    Axi4SDriver  #(AXI_DATA_WIDTH, META_WIDTH, ITEM_WIDTH) driver;
    MfbResponder #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) responder;
    MfbMonitor   #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) monitor;
    Scoreboard scoreboard;


    task createGeneratorEnvironment(int packet_size_max, int packet_size_min);
        generator = new("Generator", 0);
        blueprint = new;
        blueprint.frameSizeMax = packet_size_max;
        blueprint.frameSizeMin = packet_size_min;
        generator.blueprint = blueprint;
    endtask

    task createEnvironment();
        driver     = new("Driver", generator.transMbx, RX);
        monitor    = new("Monitor", MONITOR);
        responder  = new("Responder", TX);
        scoreboard = new;
        driver.setCallbacks(scoreboard.driverCbs);
        monitor.setCallbacks(scoreboard.monitorCbs);
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        driver.setEnabled();
        monitor.setEnabled();
        responder.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!driver.busy);
        do begin
            wait(!monitor.busy);
            fork : StayIdleWait0
                wait(monitor.busy) disable StayIdleWait0;
                #(100*CLK_PERIOD) disable StayIdleWait0;
            join
        end while(monitor.busy);
        driver.setDisabled();
        monitor.setDisabled();
        responder.setDisabled();
    endtask


    task test1(output bit status);
        bit sc_empty;

        $write("\n\n############ TEST CASE 1 ############\n\n");
        enableTestEnvironment();
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        disableTestEnvironment();
        scoreboard.display();

        // check if scoreboard is empty
        scoreboard.is_empty(sc_empty);
        // return 1 in case scoreboard is not empty
        status = sc_empty != 1;
    endtask


    initial begin
        bit status;
        resetDesign();
        createGeneratorEnvironment(FRAME_SIZE_MAX, FRAME_SIZE_MIN);
        createEnvironment();
        test1(status);

        if (status) begin
            $write("Verification Failed! Scoreboard table is not empty\n");
        end else begin
            $write("Verification finished successfully!\n");
        end
        $stop();
    end

endprogram
