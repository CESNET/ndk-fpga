/*!
 * \file sv_mfb_pkg.sv
 * \brief SystemVerilog package with Multi-Frame Bus
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

`include "mfb_ifc.sv"



package sv_mfb_pkg;

    import sv_common_pkg::*;
    import math_pkg::*;

    // SRC_RDY behaviour of MfbDriver when the word is not accepted (DST_RDY is low)
    // MFB_SRC_RDY_RELAXED - SRC_RDY can fall, the withdrawn word is sent again later
    // MFB_SRC_RDY_STRICT  - SRC_RDY must remain high until DST_RDY is high
    typedef enum {MFB_SRC_RDY_RELAXED, MFB_SRC_RDY_STRICT} src_rdy_rule_t;

    `include "mfb_transaction.sv"
    `include "mfb_monitor.sv"
    `include "mfb_responder.sv"
    `include "mfb_driver.sv"
    `include "mfb_speed.sv"

endpackage
