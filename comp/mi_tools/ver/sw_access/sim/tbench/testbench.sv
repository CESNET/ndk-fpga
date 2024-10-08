/*!
 * \file testbench.sv
 * \brief Testbench
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

import test_pkg::*;

module testbench;

  // -- Testbench wires and interfaces ----------------------------------------
  logic            RESET;
  logic            CLK = 0;
  iMi32            MI(CLK, RESET);

  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;

  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK     (CLK),
               .RESET   (RESET),
               .MI      (MI)
              );

  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.CLK        (CLK),
               .RESET      (RESET),
               .MI         (MI)
              );

endmodule : testbench
