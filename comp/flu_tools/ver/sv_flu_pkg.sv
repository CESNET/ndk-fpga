/*
 * sv_flu_pkg.sv: SystemVerilog FrameLinkUnaligned package
 * Copyright (C) 2011 CESNET
 * Author(s): Viktor Pus <pus@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

// FrameLinkUnaligned Interface
`include "flu_ifc.sv"

package sv_flu_pkg;

  import sv_common_pkg::*; // Import SV common classes
  import math_pkg::*;

  `include "flu_transaction.sv"
  `include "flu_driver.sv"
  `include "flu_driver2.sv"
  `include "flu_monitor.sv"
  `include "flu_responder.sv"
  `include "flu_command_coverage.sv"

endpackage : sv_flu_pkg
