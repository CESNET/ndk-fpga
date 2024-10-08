/*
 * sv_common_pkg.sv: SystemVerilog common package
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersk� <kobiersky@liberuter.org>
 *            Marek Santa <santa@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 * TODO:
 */


package sv_common_pkg;
  // Define boolean values
  typedef enum bit {FALSE, TRUE} bool;

  `include "transaction.sv"
  `include "generator.sv"
  `include "driver_cbs.sv"
  `include "driver.sv"
  `include "monitor_cbs.sv"
  `include "monitor.sv"
  `include "responder.sv"
  `include "transaction_table.sv"
  `include "sequence.sv"
  `include "sequencer.sv"
endpackage : sv_common_pkg
