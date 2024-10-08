/*
 * file       : pkg.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description:
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

`ifndef BLKLOCK_PKG
`define BLKLOCK_PKG

package uvm_blklock;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "model.sv"
    `include "scoreboard.sv"
    `include "env.sv"

endpackage


`endif
