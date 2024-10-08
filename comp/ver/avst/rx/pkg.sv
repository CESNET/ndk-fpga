/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

`include "interface.sv"

package avst_rx;
    `include "config.sv"
    `include "transaction.sv"
    `include "monitor.sv"
    `include "driver.sv"
    `include "agent.sv"
endpackage
