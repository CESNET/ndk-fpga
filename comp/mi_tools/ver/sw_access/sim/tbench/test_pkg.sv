/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2015
 */
 /*
 * Copyright (C) 2013 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

package test_pkg;
  // -------- CLOCKS AND RESETS ---------------------------------------------
  parameter CLK_PERIOD           = 10ns;
  parameter RESET_TIME           = 10*CLK_PERIOD;

  // -------- DUT PARAMETERS ------------------------------------------------
  parameter ITEMS                = 1024;
endpackage
