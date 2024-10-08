/*
 * dpi_test.sv:
 * Copyright (C) 2015 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

package dpi_test;
  task func_sv2c(int i);
    $write("    - fuction in SystemVerilog called with argument %0d\n", i);
  endtask;

  export "DPI-C" task func_sv2c;
  import "DPI-C" context task func_c2sv(int i);
endpackage
