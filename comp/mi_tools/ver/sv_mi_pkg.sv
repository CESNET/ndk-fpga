/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

// Frame Link Interface
`include "mi_ifc.sv"

package sv_mi_pkg;
    //define transaction types and directions
    typedef enum {TR_REQUEST, TR_RESPONSE} tr_type_t;
    typedef enum {OP_WRITE, OP_READ, OP_NONE} op_type_t;

    `include "mi_transaction.sv"
    `include "mi_driver.sv"
    `include "mi_monitor.sv"
    `include "mi_responder.sv"

    `include "mi_agent_master.sv"
    `include "mi_agent_slave.sv"

    // advanced mi_sequences
 `  include "mi_sequence.sv"

    // coverage
    `include  "mi_coverage.sv"
endpackage
