/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module DUT (
   input logic        MASTER_CLK,
   input logic        MASTER_RESET,
   iMi.master         MASTER,

   input logic        SLAVE_CLK,
   input logic        SLAVE_RESET,
   iMi.slave          SLAVE
);

// -------------------- Module body -------------------------------------------
mi_async
  VHDL_DUT_U  (

    // MI32 interface
     .CLK_M          (MASTER_CLK ),
     .RESET_M        (MASTER_RESET),
     .MI_M_DWR       (MASTER.DWR ),
     .MI_M_MWR       (MASTER.MWR ),
     .MI_M_ADDR      (MASTER.ADDR),
     .MI_M_RD        (MASTER.RD  ),
     .MI_M_WR        (MASTER.WR  ),
     .MI_M_BE        (MASTER.BE  ),
     .MI_M_DRD       (MASTER.DRD ),
     .MI_M_ARDY      (MASTER.ARDY),
     .MI_M_DRDY      (MASTER.DRDY),

    // MI32 interface
     .CLK_S          (SLAVE_CLK ),
     .RESET_S        (SLAVE_RESET),
     .MI_S_DWR       (SLAVE.DWR ),
     .MI_S_MWR       (SLAVE.MWR ),
     .MI_S_ADDR      (SLAVE.ADDR),
     .MI_S_RD        (SLAVE.RD  ),
     .MI_S_WR        (SLAVE.WR  ),
     .MI_S_BE        (SLAVE.BE  ),
     .MI_S_DRD       (SLAVE.DRD ),
     .MI_S_ARDY      (SLAVE.ARDY),
     .MI_S_DRDY      (SLAVE.DRDY)
);


endmodule : DUT
