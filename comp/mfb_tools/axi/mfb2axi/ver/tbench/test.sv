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
    iMfbRx.tb RX,
    iAxi4STx.tb TX,
    iAxi4STx.monitor MONITOR
);

    MfbTransaction #(ITEM_WIDTH) blueprint;
    Generator generator;
    MfbDriver    #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) driver;
    Axi4SResponder #(AXI_DATA_WIDTH, META_WIDTH, 8) responder; // AXI is always byte oriented
    Axi4SMonitor #(AXI_DATA_WIDTH, META_WIDTH, 8) monitor; // AXI is always byte oriented
    Scoreboard scoreboard;
    mfb_speed #(speed_cbs_rx #(ITEM_WIDTH)) mfb_speed_rx;
    mfb_speed #(speed_cbs_tx #(8)) axi_speed_tx;


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

        mfb_speed_rx = new("MFB RX");
        axi_speed_tx = new("AXI TX");

        scoreboard = new;
        driver.setCallbacks(scoreboard.driverCbs);
        monitor.setCallbacks(scoreboard.monitorCbs);

        driver.setCallbacks(mfb_speed_rx.cbs);
        monitor.setCallbacks(axi_speed_tx.cbs);

        driver.setEnabled();
        monitor.setEnabled();
        responder.setEnabled();
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
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
    endtask


    task test1(output bit status);
        bit sc_empty;

        $write("\n\n############ TEST CASE 1 ############\n\n");

        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        disableTestEnvironment();
        scoreboard.display();

        // check if scoreboard is empty
        scoreboard.is_empty(sc_empty);
        // return 1 in case scoreboard is not empty
        status = sc_empty != 1;
    endtask

    task test_speed(input int frame_size, output bit status);
        bit sc_empty;

        // enable environment
        blueprint.frameSizeMax = frame_size;
        blueprint.frameSizeMin = frame_size;
        generator.blueprint = blueprint;

        // generate TRANSACTION_COUNT
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);

        // disable environment
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

        // test 1
        test1(status);
        if (status) begin
            $write("Test1: Verification Failed! Scoreboard table is not empty\n");
            $stop();
        end

        if (ENABLE_SPEED_TEST) begin
            int speed_test_runs;

            // reset speed meters before speed meassurement (data were collected even if the speed meter was disabled)
            mfb_speed_rx.data.reset();
            axi_speed_tx.data.reset();
            mfb_speed_rx.setEnabled();
            axi_speed_tx.setEnabled();

            // if REGIONS = 1, run only bus_width + 1 byte test,
            // as the region width == bus width
            speed_test_runs = (REGIONS > 1) ? 3 : 1;

            for (int i = 0; i < speed_test_runs; i++) begin
                int frame_size;

                case (i)
                    0 : begin
                        // bus width + 1 byte with minimal inter frame gaps
                        driver.ifgEnable_wt = 0;
                        driver.wordDelayEnable_wt = 0;
                        responder.wordDelayEnable_wt = 0;
                        frame_size = REGIONS * REGION_SIZE * BLOCK_SIZE + 1;

                        $write("\n\n############ TEST SPEED ############\n");
                        $write("frame_size: %d\n", frame_size);
                        $write("inter frame gaps minimal\n");
                        $write("####################################\n");
                    end
                    1 : begin
                        // region width + 1 byte with minimal inter frame gaps
                        driver.ifgEnable_wt = 0;
                        driver.wordDelayEnable_wt = 0;
                        responder.wordDelayEnable_wt = 0;
                        frame_size = REGION_SIZE * BLOCK_SIZE + 1;

                        $write("\n\n############ TEST SPEED ############\n");
                        $write("frame_size: %d\n", frame_size);
                        $write("inter frame gaps minimal\n");
                        $write("####################################\n");
                    end
                    default : begin
                        // region width + 1 byte per transaction
                        driver.ifgEnable_wt = 1;
                        driver.ifgDisable_wt = 0;
                        driver.ifgLow  = (REGIONS-1) * REGION_SIZE - 1;
                        driver.ifgHigh = (REGIONS-1) * REGION_SIZE - 1;
                        driver.wordDelayEnable_wt = 0;
                        responder.wordDelayEnable_wt = 0;
                        frame_size = REGION_SIZE * BLOCK_SIZE + 1;

                        $write("\n\n############ TEST SPEED ############\n");
                        $write("frame_size: %d\n", frame_size);
                        $write("inter frame gaps set to fill the bus (1 frame per cycle)\n");
                        $write("####################################\n");
                    end
                endcase;

                test_speed(frame_size, status);
                if (status) begin
                    $write("Test Speed (%d): Verification Failed! Scoreboard table is not empty\n", i);
                    $stop();
                end
            end
        end

        if (!status) begin
            $write("Verification finished successfully!\n");
        end

        driver.setDisabled();
        monitor.setDisabled();
        responder.setDisabled();

        if (ENABLE_SPEED_TEST) begin
            mfb_speed_rx.setDisabled();
            axi_speed_tx.setDisabled();
        end

        $stop();
    end

endprogram
