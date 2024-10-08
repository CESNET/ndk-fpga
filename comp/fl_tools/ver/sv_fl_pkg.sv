/*
 * sv_fl_pkg.sv: SystemVerilog FrameLink package
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobierský <kobiersky@liberuter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 * TODO:
 */

// Frame Link Interface
`include "fl_ifc.sv"

package sv_fl_pkg;

  import sv_common_pkg::*; // Import SV common classes

  `include "fl_transaction.sv"
  `include "fl_driver.sv"
  `include "fl_monitor.sv"
  `include "fl_responder.sv"
  `include "fl_command_coverage.sv"

endpackage : sv_fl_pkg
