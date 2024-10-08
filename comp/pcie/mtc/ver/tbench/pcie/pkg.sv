/*
 * pkg.sv  pcie2mi packaga
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

`include "interface.sv"

package pcie2mi;

    `include "transaction.sv"
    `include "base.sv"
    `include "axi.sv"
    `include "avalon.sv"

    `include "root.sv"

    `include "sequence.sv"
endpackage
