/*!
 * \file sv_axi_pkg.sv
 * \brief SystemVerilog package with Multi-Frame Bus
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

`include "axi_ifc.sv"

package sv_axi_pkg;

    import sv_common_pkg::*;
    import math_pkg::*;

    `include "axi_transaction.sv"
    `include "axi_driver.sv"
    `include "axi_monitor.sv"
    `include "axi_responder.sv"

endpackage
