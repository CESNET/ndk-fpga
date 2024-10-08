/*
 * nfbctl.c: DPI example tool using NFB-like access
 * Copyright (C) 2018 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

#include <stdio.h>
#include <stdlib.h>

#include <nfb/nfb.h>



int main(int argc, char *argv[]) {
    printf("Memory test3:\n");
    unsigned x, items;
    if(argc <= 1)
        items = 1024;
    else
        items = atoi(argv[1]);
    printf("    size = %d\n", items);

    int unsigned buf[items];
    char *path = NFB_PATH_DEV(0);
    struct nfb_device *dev;
    struct nfb_comp *comp;
    int node;

    dev = nfb_open(path);
    node = nfb_comp_find(dev, "netcope,memory", 0);
    comp = nfb_comp_open(dev, node);

    for(unsigned i=0; i<items; i++) {
        nfb_comp_write32(comp, i<<2, i+0xbeef0000);
        x = nfb_comp_read32(comp, i<<2);
        if(x != i+0xbeef0000)
            printf("mismatch: %d != %d\n", x, i+0xbeef0000);
    }

    nfb_comp_read(comp, buf, items<<2, 0);
    for(unsigned i=0; i<items; i++) {
        if(buf[i] != i+0xbeef0000)
            printf("mismatch: %d != %d\n", x, i+0xbeef0000);
    }

    nfb_comp_close(comp);
    nfb_close(dev);
    printf("    Done.\n");
    return 0;
}



// /////////////////////////////////////////////////////////////////////////////
// Verification specific implementation:
__attribute__((visibility("default"))) int nfbctl(int argc, char *argv[]) {
    return main(argc,argv);
}

void dpiregister(const char *name, int (*main)(int argc, char *argv[]));

void __dpiregisterself() {
    dpiregister("nfbctl", nfbctl);
}
// /////////////////////////////////////////////////////////////////////////////
