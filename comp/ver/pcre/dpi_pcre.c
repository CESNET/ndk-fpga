/*
 * dpi_pcre.c: Wrapper of libPCRE for SystemVerilog
 * Copyright (C) 2016 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

#include <pcre.h>
#include "svdpi.h"
#include "dpi_pcre.h"

void* dpi_pcre_compile(const char* pattern, int options, const char** errptr, int* erroffset, const char* tableptr) {
    if(tableptr && tableptr[0] == '\0')
        tableptr = NULL;
    return pcre_compile(pattern, options, errptr, erroffset, tableptr);
}

void dpi_pcre_free(void* pcre) {
    pcre_free(pcre);
}

int dpi_pcre_exec(void* code, void* extra, const svOpenArrayHandle subject, int length, int startoffset, int options, const svOpenArrayHandle ovector, int ovecsize) {
    int ov[ovecsize], ret;
    ret = pcre_exec(code, extra, (unsigned char *)svGetArrayPtr(subject), length, startoffset, options, ov, ovecsize);
    for(int i = 0; i < ovecsize; i++)
        *((int *)svGetArrElemPtr1(ovector, i)) = ov[i];
    return ret;
}
