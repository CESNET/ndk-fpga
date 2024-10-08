/**
 * \file sv_flup_pkg.sv.sv
 * \brief FrameLinkUnaligned Plus Package
 * \author Jan Kučera <xkucer73@stud.fit.vutbr.cz>
 * \date 2015
 */

/**
 * Copyright (C) 2015 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id:
 *
 */

// FrameLinkUnaligned Plus Interface
`include "flup_ifc.sv"

/**
 * FrameLinkUnaligned Plus Package declaration
 */
package sv_flup_pkg;

   import sv_common_pkg::*;

   `include "flup_transaction.sv"
   `include "flup_driver.sv"
   `include "flup_monitor.sv"
   `include "flup_responder.sv"

endpackage : sv_flup_pkg
