/*
 * sv_discard_stat_pkg.sv: SystemVerilog FrameLink Discard Stat package
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberuter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 * TODO:
 */

// FrameLink Discard Stat Interface
`include "discard_stat_ifc.sv"

package sv_discard_stat_pkg;

  import sv_common_pkg::*; // Import SV common classes
  import sv_fl_pkg::*; // Import SV FrameLink classes

  `include "fl_multiplexor.sv"
  `include "fl_demultiplexor.sv"
  `include "discard_stat_scoreboard.sv"
  `include "discard_stat_discarding_model.sv"

endpackage : sv_discard_stat_pkg
