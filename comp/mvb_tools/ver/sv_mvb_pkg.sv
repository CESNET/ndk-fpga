/*!
 * \file sv_mvb_pkg.sv
 * \brief SystemVerilog package with Multi-Value Bus
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

`include "mvb_ifc.sv"



package sv_mvb_pkg;

    import sv_common_pkg::*;


    `include "mvb_transaction.sv"
    `include "mvb_monitor.sv"
    `include "mvb_responder.sv"
    `include "mvb_driver.sv"
    `include "mvb_coverage.sv"

endpackage
