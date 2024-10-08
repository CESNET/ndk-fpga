/*
 * sv_f2f_pkg.sv: SystemVerilog Fifo2nFifo package
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 * TODO:
 */

// Fifo2nFifo Interface
`include "buffer_ifc.sv"

package sv_buffer_pkg;

  import sv_common_pkg::*; // Import SV common classes

  `include "buffer_transaction.sv"
  `include "fifo_driver.sv"
  `include "nfifo_driver.sv"
  `include "mem_driver.sv"
  `include "fifo_monitor.sv"
  `include "nfifo_monitor.sv"
  `include "mem_monitor.sv"
  `include "mem_monitor_new.sv"
  `include "fifo_responder.sv"
  `include "nfifo_responder.sv"
  `include "mem_responder.sv"

endpackage : sv_buffer_pkg
