/*!
 * \file test.sv
 * \brief Test Cases
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2015
 */
 /*
 * Copyright (C) 2015 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import dpi_sw_access::*;
import test_pkg::*;

// ----------------------------------------------------------------------------
//                            Testing Program
// ----------------------------------------------------------------------------
program TEST (
  input  logic     CLK,
  output logic     RESET,
  iMi32.tb         MI
);

  // --------------------------------------------------------------------------
  //                           Main test part
  // --------------------------------------------------------------------------
  initial begin
    int ret;
    string params;
    dpiconnect(0, MI);
    dpiconnect_setinfo(0, 'hffffffff, "combo_sim", "combo_sim_memtest", 'h12345678, 'h90abcdef);
    dpiconnect_addcomponent(0, "memory", 'h00010004, 0, ITEMS*4);
    ret = dpiconnect_devicetree_addcomponent(0, "\
      memory {\
        compatible = \"netcope,memory\";\
        reg = <0x0 0x10000>;\
        version = <0x10004>;\
      };");
    if(!ret)
      $write("DeviceTree error!!!\n");
    dpiconnect_display(0);
    dpiconnect_devicetree_display(0);
    RESET=1;
    #RESET_TIME     RESET = 0;
    params = $sformatf( "%0d", ITEMS);
    dpicall("paramsctl", params, ret);
    dpicall("directctl", params, ret);
    dpicall("comboctl", params, ret);
    dpicall("nfbctl", params, ret);
    $stop();
  end

endprogram

