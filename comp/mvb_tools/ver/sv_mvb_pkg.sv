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

    // SRC_RDY behaviour of MvbDriver when the word is not accepted (DST_RDY is low)
    // MVB_SRC_RDY_RELAXED - SRC_RDY can fall, the withdrawn word is sent again later
    // MVB_SRC_RDY_STRICT  - SRC_RDY must remain high until DST_RDY is high
    typedef enum {MVB_SRC_RDY_RELAXED, MVB_SRC_RDY_STRICT} src_rdy_rule_t;

    `include "mvb_transaction.sv"
    `include "mvb_monitor.sv"
    `include "mvb_responder.sv"
    `include "mvb_driver.sv"
    `include "mvb_coverage.sv"
    `include "mvb_speed.sv"

endpackage
