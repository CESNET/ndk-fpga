/*!
 * \file test.sv
 * \brief Test Cases
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2017 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import sv_common_pkg::*;
import sv_wl_pkg::*;
import test_pkg::*;



program TEST (
    input logic CLK,
    output logic RESET,
    iWordLinkRx.tb RX
);


    WordLinkTransaction blueprint;
    Generator generator;
    WordLinkDriver #(2*CARRY_WIDTH+1) driver;


    task createGeneratorEnvironment();
        generator = new("Generator", 0);
        blueprint = new;
        blueprint.dataSize = (2*CARRY_WIDTH+1-1)/8 + 1;
        generator.blueprint = blueprint;
    endtask

    task createEnvironment();
        driver  = new("Driver", generator.transMbx, RX);
        driver.txDelayEn_wt = 0;
    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        driver.setEnabled();
    endtask

    task disableTestEnvironment();
        wait(!driver.busy);
        driver.setDisabled();
    endtask


    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        enableTestEnvironment();
        generator.setEnabled(TRANSACTION_COUNT);
        wait(!generator.enabled);
        disableTestEnvironment();
    endtask


    initial begin
        resetDesign();
        createGeneratorEnvironment();
        createEnvironment();
        test1();
        $stop();
    end

endprogram

