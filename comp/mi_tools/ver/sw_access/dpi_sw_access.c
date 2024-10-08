/*
 * dpi_sw_access.c: Software (C/C++) tool calling through DPI
 * Copyright (C) 2015 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

#include <stdlib.h>
#include <stdio.h>
#include <svdpi.h>
#include <unistd.h>
#include <getopt.h>
#include <ctype.h>

static int DPITOOLS = 0;

static char **DPITOOLS_NAMES = NULL;

int (**DPITOOLS_FUNCTIONS)(int argc, char *argv[]) = NULL;

__attribute__((visibility("default"))) void dpiregister(const char *name, int (*main)(int argc, char *argv[])) {
    for(int i=0; i<DPITOOLS; i++) {
        if(strcmp(DPITOOLS_NAMES[i],name) == 0) {
            DPITOOLS_FUNCTIONS[i] = main;
            return;
        }
    }
    DPITOOLS++;
    void *tmp = NULL;
    tmp = realloc(DPITOOLS_NAMES, sizeof(char *)*DPITOOLS);
    if(!tmp) {
        fprintf(stderr,"dpiregister: Out of memory!!!\n");
        return;
    }
    DPITOOLS_NAMES = tmp;
    int slen = strlen(name)+1;
    DPITOOLS_NAMES[DPITOOLS-1] = NULL;
    tmp = malloc(sizeof(char)*slen);
    if(!tmp) {
        fprintf(stderr,"dpiregister: Out of memory!!!\n");
        return;
    }
    memcpy(tmp,name,slen);
    DPITOOLS_NAMES[DPITOOLS-1] = tmp;
    tmp = realloc(DPITOOLS_FUNCTIONS, sizeof(int (*)(int argc, char *argv[]))*DPITOOLS);
    if(!tmp) {
        fprintf(stderr,"dpiregister: Out of memory!!!\n");
        return;
    }
    DPITOOLS_FUNCTIONS = tmp;
    DPITOOLS_FUNCTIONS[DPITOOLS-1] = main;
}

void dpiclear() {
    if(DPITOOLS_NAMES) {
        for(int i=0; i<DPITOOLS; i++)
            if(DPITOOLS_NAMES[i])
                free(DPITOOLS_NAMES[i]);
        free(DPITOOLS_NAMES);
    }
    if(DPITOOLS_FUNCTIONS)
        free(DPITOOLS_FUNCTIONS);
}

int dpicalldispatch(const char *name, int argc, char *argv[]) {
    for(register unsigned i = 0; i<DPITOOLS; i++) {
        if(strcmp(DPITOOLS_NAMES[i],name) == 0) return DPITOOLS_FUNCTIONS[i](argc,argv);
    }
    printf("dpicall error: unknown tool '%s'!!!\n", name);
    return -1;
}

__attribute__((visibility("default"))) int dpicall(const char* name, const char* params, int* retval) {
    int argc = 1, size = strlen(params) + 1, name_size = strlen(name) + 1;
    char **argv = NULL;
    char *buffer = NULL;
    char *ptr;
    int space = 1, quote = 0;
    buffer = malloc(size+name_size);
    if(buffer == NULL) {
        fprintf(stderr,"dpicall: Out of memory!!!\n");
        *retval = -1;
        return 0;
    }
    memcpy(buffer, name, name_size);
    ptr = buffer + name_size;
    memcpy(ptr, params, size);
    for(int i=0; i<size-1; i++)
        if(isspace(ptr[i])) {
            if(!quote) {
                space = 1;
                ptr[i] = '\0';
            }
        } else {
            if(space)
                argc++;
            if(ptr[i] == '"') {
                quote = !quote;
                ptr[i] = '\0';
            }
            space = 0;
        }
    argv = malloc(argc*sizeof(char*));
    if(argv == NULL) {
        fprintf(stderr,"dpicall: Out of memory!!!\n");
        *retval = -1;
        free(buffer);
        return 0;
    }
    argv[0] = buffer;
    if(argc > 1) {
        space = 1;
        for(int j=0, k=1; j<size; j++) {
            if(ptr[j] == '\0')
                space = 1;
            else {
                if(space)
                    argv[k++] = ptr + j;
                space = 0;
            }
        }
    }
    printf("dpicall: %s %s\n", name, params);
    optind = 0;
    *retval = dpicalldispatch(name,argc,argv);
    fflush(stdout);
    free(buffer);
    free(argv);
    return 0;
}
