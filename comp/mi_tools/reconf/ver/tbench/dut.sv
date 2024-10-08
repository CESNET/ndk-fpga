/*
 * Copyright (C) 2021 CESNET z. s. p. o.
 * Author(s): Jan Kubalek <kubalek@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module DUT (
    input logic CLK,
    input logic RESET,
    iMi.master  RX,
    iMi.slave   TX
);

// -------------------- Module body -------------------------------------------
MI_RECONFIGURATOR #(
    .RX_DATA_WIDTH (RX_DATA_WIDTH),
    .TX_DATA_WIDTH (TX_DATA_WIDTH),
    .ADDR_WIDTH    (ADDR_WIDTH   ),
    .META_WIDTH    (META_WIDTH   )
)
VHDL_DUT_U (

    .CLK          (CLK ),
    .RESET        (RESET),

    .RX_DWR       (RX.DWR ),
    .RX_MWR       (RX.MWR ),
    .RX_ADDR      (RX.ADDR),
    .RX_RD        (RX.RD  ),
    .RX_WR        (RX.WR  ),
    .RX_BE        (RX.BE  ),
    .RX_DRD       (RX.DRD ),
    .RX_ARDY      (RX.ARDY),
    .RX_DRDY      (RX.DRDY),

    .TX_DWR       (TX.DWR ),
    .TX_MWR       (TX.MWR ),
    .TX_ADDR      (TX.ADDR),
    .TX_RD        (TX.RD  ),
    .TX_WR        (TX.WR  ),
    .TX_BE        (TX.BE  ),
    .TX_DRD       (TX.DRD ),
    .TX_ARDY      (TX.ARDY),
    .TX_DRDY      (TX.DRDY)
);

endmodule : DUT
