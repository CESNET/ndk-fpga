/*
 * file       : pkg.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: General MII UVM package
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef MII_PKG_SV
`define MII_PKG_SV

package uvm_mii;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "config.sv"
    `include "sequence_item.sv"
    `include "sequencer.sv"
    `include "monitor.sv"
    `include "driver.sv"
    `include "agent.sv"

endpackage

`endif
