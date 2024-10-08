/*
 * dpi_pcap.sv: Wrapper of libPCRE for SystemVerilog
 * Copyright (C) 2016 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

package dpi_pcre;

    typedef chandle dpi_pcre_t;
    typedef chandle dpi_pcre_extra_t;

    // constants from pcre.h
    parameter DPI_PCRE_CASELESS       = 'h0001;
    parameter DPI_PCRE_MULTILINE      = 'h0002;
    parameter DPI_PCRE_DOTALL         = 'h0004;
    parameter DPI_PCRE_EXTENDED       = 'h0008;
    parameter DPI_PCRE_ANCHORED       = 'h0010;
    parameter DPI_PCRE_DOLLAR_ENDONLY = 'h0020;
    parameter DPI_PCRE_EXTRA          = 'h0040;
    parameter DPI_PCRE_NOTBOL         = 'h0080;
    parameter DPI_PCRE_NOTEOL         = 'h0100;
    parameter DPI_PCRE_UNGREEDY       = 'h0200;
    parameter DPI_PCRE_ERROR_NOMATCH      = (-1);
    parameter DPI_PCRE_ERROR_NULL         = (-2);
    parameter DPI_PCRE_ERROR_BADOPTION    = (-3);
    parameter DPI_PCRE_ERROR_BADMAGIC     = (-4);
    parameter DPI_PCRE_ERROR_UNKNOWN_NODE = (-5);
    parameter DPI_PCRE_ERROR_NOMEMORY     = (-6);
    parameter DPI_PCRE_ERROR_NOSUBSTRING  = (-7);

    import "DPI-C" context function dpi_pcre_t dpi_pcre_compile(string pattern, int options, output string errptr, output int erroffset, input string tableptr);
    import "DPI-C" context function void dpi_pcre_free(dpi_pcre_t pcre);
    import "DPI-C" context function int dpi_pcre_exec(dpi_pcre_t code, dpi_pcre_extra_t extra, byte unsigned subject[], int length, int startoffset, int options, output int ovector[], input int ovecsize);

endpackage
