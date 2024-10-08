/*
 * paramsctl.c: Simple DPI tool to display passed arguments
 * Copyright (C) 2015 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

#include <stdio.h>
#include <stdlib.h>

int main(int argc, const char *argv[]) {
    printf("DPI called tool with arguments:\n");
    for(int i=0; i<argc; i++) {
        printf("    - argument #%d is '%s'\n", i, argv[i]);
    }
    return 0;
}



// /////////////////////////////////////////////////////////////////////////////
// Verification specific implementation:
__attribute__((visibility("default"))) int paramsctl(int argc, const char *argv[]) {
    return main(argc,argv);
}

void dpiregister(const char *name, int (*main)(int argc, const char *argv[]));

void __dpiregisterself() {
    dpiregister("paramsctl",paramsctl);
}
// /////////////////////////////////////////////////////////////////////////////
