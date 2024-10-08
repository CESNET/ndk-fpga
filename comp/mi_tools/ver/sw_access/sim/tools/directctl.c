/*
 * directctl.c: DPI example tool using direct access (no combo)
 * Copyright (C) 2015 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

#include <stdio.h>
#include <stdlib.h>

#include "../../dpi_sw_access.h"

int main(int argc, const char *argv[]) {
    printf("Memory test:\n");
    unsigned x, items;
    if(argc <= 1)
        items = 1024;
    else
        items = atoi(argv[1]);
    printf("    size = %d\n", items);

    for(unsigned i=0; i<items; i++) {
        dpiwrite(0, i<<2, i);
        dpiread(0, i<<2, &x);
        if(x != i)
            printf("mismatch: %d != %d\n", x, i);
    }

    dpiwait(0, 100);

    for(unsigned i=0; i<items; i++) {
        dpiread(0, i<<2, &x);
        if(x != i)
            printf("mismatch: %d != %d\n", x, i);
    }
    printf("    Done.\n");
    return 0;
}



// /////////////////////////////////////////////////////////////////////////////
// Verification specific implementation:
__attribute__((visibility("default"))) int directctl(int argc, const char *argv[]) {
    return main(argc,argv);
}

void dpiregister(const char *name, int (*main)(int argc, const char *argv[]));

void __dpiregisterself() {
    dpiregister("directctl", directctl);
}
// /////////////////////////////////////////////////////////////////////////////
