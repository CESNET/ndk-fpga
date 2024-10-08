/*!
 * \file test.sv
 * \brief Test Cases
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import dpi_sw_access::*;
import sv_common_pkg::*;


program TEST (
    input  logic     CLK,
    output logic     RESET,
    iMi32.tb         MI
);


    task createEnvironment();
        dpiconnect(0, MI);
        dpiconnect_devicetree_addcomponent(0, {"\
            replay {\
                compatible = \"netcope,busreplay\";\
                reg = <0x0 0x200>;\
            };"});
    endtask

    task resetDesign();
        RESET=1;
        #100ns RESET = 0;
    endtask

    task configDesign();
        int ret;
        string params;
        params = $sformatf("-w %s", "dump.txt"); // EDIT THIS: change file path!
        dpiwait(0, 1); // synchronization
        dpicall("busreplay", params, ret);
    endtask

    task enableTestEnvironment();
        int ret;
        dpiwait(0, 1); // synchronization
        dpicall("busreplay", "-e 1", ret);
    endtask


    initial begin
        resetDesign();
        createEnvironment();
        configDesign();
        enableTestEnvironment();
        wait (0);
    end

endprogram

