/*
 * sv_pcd_pkg.sv: SystemVerilog PACODAG package
 * Copyright (C) 2007 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 * TODO:
 */

// PACODAG Interface
`include "pcd_ifc.sv"

package sv_pcd_pkg;

  import sv_common_pkg::*; // Import SV common classes

  `include "pcd_transaction.sv"
  `include "pcd_driver.sv"
  `include "pcd_monitor.sv"

endpackage : sv_pcd_pkg
