// sv_rb_pkg.sv: SystemVerilog package with Read Bus
// Copyright (C) 2024 CESNET z. s. p. o.
// Author: Tomas Hak <hak@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

package sv_rb_pkg;

    import sv_common_pkg::*;
    import sv_mvb_pkg::*;

    `include "rb_transaction.sv"

endpackage
