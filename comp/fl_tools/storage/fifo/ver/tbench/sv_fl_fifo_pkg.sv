/*
 * sv_fl_fifo_pkg.sv: SystemVerilog FL_FIFO package
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 * TODO:
 */

// FrameLink FIFO Control Interface
`include "fl_fifo_ifc.sv"

package sv_fl_fifo_pkg;

  `include "fl_fifo_ctrl_checker.sv"
  `include "fl_fifo_ctrl_cover.sv"

endpackage : sv_fl_fifo_pkg
