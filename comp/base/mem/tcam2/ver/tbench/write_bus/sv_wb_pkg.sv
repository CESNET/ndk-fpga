// sv_wb_pkg.sv: SystemVerilog package with Write Bus
// Copyright (C) 2020 CESNET z. s. p. o.
// Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

`include "wb_ifc.sv"

package sv_wb_pkg;

    import sv_common_pkg::*;

    `include "wb_transaction.sv"
    `include "wb_driver.sv"

endpackage
