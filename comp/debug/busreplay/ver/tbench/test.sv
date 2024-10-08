/*!
 * \file test.sv
 * \brief Test Cases
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import dpi_sw_access::*;
import sv_common_pkg::*;
import sv_flu_pkg::*;
import test_pkg::*;



program TEST (
    output logic          RESET,
    iFrameLinkURx.tb      RX,
    iFrameLinkUTx.tb      TX,
    iMi32.tb              MI_DUMP,
    iMi32.tb              MI_REPLAY
);


    Generator generator;
    FrameLinkUTransaction fluBlueprint;
    FrameLinkUDriver #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) fluDriver;
    FrameLinkUMonitor #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) fluMonitor;
    FrameLinkUResponder #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) fluResponder;
    Scoreboard scoreboard;


    task createEnvironment();
        scoreboard = new;
        fluBlueprint = new;
        fluBlueprint.packetSizeMax = (DATA_WIDTH/8)*4;
        fluBlueprint.packetSizeMin = (DATA_WIDTH/8)/2;
        generator = new("Generator", 0);
        generator.blueprint = fluBlueprint;
        fluDriver = new ("Driver", generator.transMbx, RX);
        fluDriver.insideTxDelayEn_wt = 3;
        fluDriver.insideTxDelayDisable_wt = 1;
        fluDriver.insideTxDelayLow = 1;
        fluDriver.insideTxDelayHigh = 31;
        fluDriver.setCallbacks(scoreboard.driverCbs);
        fluMonitor = new ("Monitor", TX);
        fluMonitor.setCallbacks(scoreboard.monitorCbs);
        fluResponder = new ("Responder", TX);
        fluResponder.rxDelayEn_wt            = 0;
        fluResponder.insideRxDelayEn_wt      = 0;
        dpiconnect(0, MI_DUMP);
        dpiconnect_devicetree_addcomponent(0, {"\
            dump {\
                compatible = \"netcope,busdump\";\
                reg = <0x0 0x200>;\
            };"});
        dpiconnect(1, MI_REPLAY);
        dpiconnect_devicetree_addcomponent(1, {"\
            replay {\
                compatible = \"netcope,busreplay\";\
                reg = <0x0 0x200>;\
            };"});
    endtask : createEnvironment


    task resetDesign();
        RESET = 1;
        #100ns RESET = 0;
    endtask : resetDesign


    task enableTestEnvironment();
        fluDriver.setEnabled();
        fluMonitor.setEnabled();
        fluResponder.setEnabled();
    endtask : enableTestEnvironment


    task test(int i);
        int ret;
        $write("\n\n############ TEST CASE %0d ############\n\n", i);
        dpiwait(0, 1); dpicall("busdump", "-d DeviceTree-dut0.dtb -e 1", ret);
        generator.setEnabled(ITEMS/8);
        wait(!generator.enabled);
        ret = 0;
        while(ret<100) begin
            if(fluDriver.busy)
                ret = 0;
            else
                ret++;
            dpiwait(0, 1);
        end
        dpiwait(0, 1); dpicall("busdump", "-d DeviceTree-dut0.dtb -e 0", ret);
        dpiwait(0, 1); dpicall("busdump", "-d DeviceTree-dut0.dtb -r dump.txt", ret);
        dpiwait(0, 1); dpicall("busreplay", "-d DeviceTree-dut1.dtb -w dump.txt", ret);
        dpiwait(0, 1); dpicall("busreplay", "-d DeviceTree-dut1.dtb -e 1", ret);
        ret = 0;
        while(ret<100) begin
            if(fluMonitor.busy)
                ret = 0;
            else
                ret++;
            dpiwait(0, 1);
        end
        dpiwait(0, 1); dpicall("busreplay", "-d DeviceTree-dut1.dtb -e 0", ret);
        scoreboard.display();
  endtask: test


  initial begin
    resetDesign();
    createEnvironment();
    enableTestEnvironment();
    for(int i=0; 1; i++)
        test(i);
    $stop();
  end

endprogram

