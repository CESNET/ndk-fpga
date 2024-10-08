/*
 * dpi_sw_access.c: Software (C/C++) tool calling through DPI
 * Copyright (C) 2015 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

#include <stdio.h>

#include <svdpi.h>

#include "dpi_test.h" // automaticky generovany pri preklade z dpi_test.sv

int func_c2sv(int i) {
    printf("    - function in C called with argument %0d\n", i);
    printf("\nC calling SystemVerilog function with argument +1:\n");
    func_sv2c(i + 1);
}
