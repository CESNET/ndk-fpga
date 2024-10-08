/*
 * file       : program.c
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: call program in different threads to comunicate with simulation
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

#define _GNU_SOURCE
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

static void * run_program(void *arg) {
    char * cmd = arg;

    unsigned int *ret_code;

    ret_code = malloc(sizeof (unsigned int));
    if (ret_code == NULL) {
        return NULL;
    }

    *ret_code = system(cmd);
    free(arg);
    return ret_code;
}

void * dpi_program_call(const char * cmd)
{
    pthread_t *ret;
    char * cmd_cpy;
    unsigned int cmd_len;

    ret = malloc(sizeof(pthread_t));
    if (ret == NULL) {
        return NULL;
    }

    cmd_len = strlen(cmd) + 1;
    cmd_cpy = malloc(sizeof(*cmd_cpy) * cmd_len);
    if (cmd_cpy == NULL) {
        free(ret);
        return NULL;
    }
    memcpy(cmd_cpy, cmd, cmd_len);

    int pt_ret = pthread_create(ret, NULL, run_program, cmd_cpy);
    if (pt_ret != 0) {
        free(cmd_cpy);
        free(ret);
        return NULL;
    }

    return ret;
}

int dpi_program_wait(void * prg)
{
    int ret;
    unsigned int *ret_val;
    pthread_t *id = prg;

    if (pthread_tryjoin_np(*id, (void **) &ret_val) != 0) {
        ret = -1;
    } else {
        ret = *ret_val;
        free(ret_val);
    }
    return ret;
}


#undef _GNU_SOURCE


