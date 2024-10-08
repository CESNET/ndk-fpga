/*
 * test.sv:
 * Copyright (C) 2015 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import dpi_test::*;



module testbench();

    initial begin
        $write("\nSystemVerilog calling C function:\n");
        func_c2sv(10);
        $write("\n");
    end

endmodule

