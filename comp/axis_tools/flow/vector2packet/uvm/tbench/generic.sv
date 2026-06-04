// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>
// SPDX-License-Identifier: BSD-3-Clause

package uvm_generic;
    parameter int unsigned RX_TDATA_WIDTH     = 64;
    parameter int unsigned TX_TDATA_WIDTH     = 64;
    parameter int unsigned TUSER_WIDTH        = 64;

    parameter int unsigned RX_ITEM_WIDTH      = RX_TDATA_WIDTH;
    parameter int unsigned RX_ITEMS           = 1;

    parameter int unsigned TX_ITEM_WIDTH      = 8;
    parameter int unsigned TX_ITEMS           = TX_TDATA_WIDTH / TX_ITEM_WIDTH;

    parameter time CLK_PERIOD = 4ns;
endpackage
