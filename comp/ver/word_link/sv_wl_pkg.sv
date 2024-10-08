/*
 * sv_wl_pkg.sv: SystemVerilog Word Link protocol package
 *(word by word data transporting protocol with source and destination ready signalization)
 * Copyright (C) 2015 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

`include "wl_ifc.sv"

package sv_wl_pkg;

  import sv_common_pkg::*; // Import SV common classes

  `include "wl_transaction.sv"
  `include "wl_driver.sv"
  `include "wl_monitor.sv"
  `include "wl_meter.sv"
  `include "wl_responder.sv"

endpackage : sv_wl_pkg
