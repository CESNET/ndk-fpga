/*
 * comboctl.c: DPI example tool using combo-like access
 * Copyright (C) 2015 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

#include <stdio.h>
#include <stdlib.h>

#include <combo.h>
#include <commlbr.h>

int main(int argc, char *argv[]) {
    printf("Memory test2:\n");
    unsigned x, items;
    if(argc <= 1)
        items = 1024;
    else
        items = atoi(argv[1]);
    printf("    size = %d\n", items);

    int unsigned buf[items];
    char           *file = CS_PATH_DEV(0);
    cs_device_t    *dev;
    cs_component_t *comp_id;
    cs_space_t     *master_space;
    cs_attach_noex(&dev, file);
    cs_design_reload(dev, CS_DESIGN_XML, NULL);
    cs_component_find(dev, &comp_id, NULL, "memory", 0);
    cs_component_space(comp_id, &master_space);

    for(unsigned i=0; i<items; i++) {
        cs_space_write_4(dev, master_space, i<<2, i+0xdead0000);
        x = cs_space_read_4(dev, master_space, i<<2);
        if(x != i+0xdead0000)
            printf("mismatch: %d != %d\n", x, i+0xdead0000);
    }

    cs_space_read_multi_4(dev, master_space, 0, items, buf);
    for(unsigned i=0; i<items; i++) {
        if(buf[i] != i+0xdead0000)
            printf("mismatch: %d != %d\n", x, i+0xdead0000);
    }
    printf("    Done.\n");
    return 0;
}



// /////////////////////////////////////////////////////////////////////////////
// Verification specific implementation:
__attribute__((visibility("default"))) int comboctl(int argc, char *argv[]) {
    return main(argc,argv);
}

void dpiregister(const char *name, int (*main)(int argc, char *argv[]));

void __dpiregisterself() {
    dpiregister("comboctl", comboctl);
}
// /////////////////////////////////////////////////////////////////////////////
