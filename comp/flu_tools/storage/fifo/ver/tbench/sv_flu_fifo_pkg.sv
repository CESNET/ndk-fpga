/*
 * sv_flu_fifo_pkg.sv: SystemVerilog FLU_FIFO package
 * Copyright (C) 2012 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 * TODO:
 */

// Frame Link Unaligned FIFO Control Interface
`include "flu_fifo_ifc.sv"

package sv_flu_fifo_pkg;

  `include "flu_fifo_ctrl_checker.sv"

endpackage : sv_flu_fifo_pkg
