/*!
 * \file test.sv
 * \brief Test Cases
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import dpi_pcre::*;



module testbench();

    initial begin
        dpi_pcre_t pcre;
        string errMsg;
        byte unsigned t1[], t2[], t3[];
        int errOff, pos[30], ret;

        pcre = dpi_pcre_compile("^a*b*c*$", DPI_PCRE_DOTALL, errMsg, errOff, "");
        if(pcre == null) begin
            $write("ERROR: expression compilation failed on position %0d - %s\n", errOff, errMsg);
            $stop;
        end else
            $write("Expression compiled!\n");

        t1 = "aaaabbcccccc";
        t2 = "acb";
        t3 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaac";

        ret = dpi_pcre_exec(pcre, null, t1, t1.size, 0, 0, pos, 30);
        if(ret < 0)
            if(ret == DPI_PCRE_ERROR_NOMATCH)
                $write("  t1 do not match!\n");
            else
                $write("  t1 ERROR!!!\n");
        else
            $write("  t1 do match!\n");
        ret = dpi_pcre_exec(pcre, null, t2, t2.size, 0, 0, pos, 30);
        if(ret < 0)
            if(ret == DPI_PCRE_ERROR_NOMATCH)
                $write("  t2 do not match!\n");
            else
                $write("  t2 ERROR!!!\n");
        else
            $write("  t2 do match!\n");
        ret = dpi_pcre_exec(pcre, null, t3, t3.size, 0, 0, pos, 30);
        if(ret < 0)
            if(ret == DPI_PCRE_ERROR_NOMATCH)
                $write("  t3 do not match!\n");
            else
                $write("  t3 ERROR!!!\n");
        else
            $write("  t3 do match!\n");

        dpi_pcre_free(pcre);
    end

endmodule

