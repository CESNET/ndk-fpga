/*
 * file       : nfb_driver.c
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: create interprocess comunication with nfb program. This framework use POSIX queue
 * date       : 2022
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

#include "svdpi.h"
#include <stdio.h>
#include <mqueue.h>
#include <stdlib.h>
#include <errno.h>

#include "nfb_driver.h"

void * nfb_sv_create(const char * path, int unsigned msg_size)
{
    nfb_sv_struct_t *ret;
    struct mq_attr attr;
    unsigned int name_size;

    name_size = strlen(path);
    ret = malloc(sizeof (*ret));
    if (ret == NULL) {
        return NULL;
    }
    ret->buff_size = 0;
    ret->req = -1;
    ret->res = -1;

    ret->buff_size = msg_size;
    ret->buff = malloc(msg_size);
    if (ret->buff == NULL) {
        nfb_sv_close(ret, path);
        return NULL;
    }

    // REQUEST
    attr.mq_flags   = 0;
    attr.mq_maxmsg  = 2;
    attr.mq_msgsize = msg_size;
    attr.mq_curmsgs = 0;

    memcpy(ret->buff, path, name_size);
    memcpy(ret->buff + name_size, "_req", 5);
    ret->req = mq_open(ret->buff, O_CREAT | O_RDONLY | O_EXCL | O_NONBLOCK, 0600, &attr);
    if (ret->req == -1) {
        fprintf(stdout, "Cannot create %s : %s\n", ret->buff, strerror(errno));
        fflush(stdout);
        nfb_sv_close(ret, path);
        return NULL;
    }

    // RESPONSE
    attr.mq_flags   = 0;
    attr.mq_maxmsg  = 2;
    attr.mq_msgsize = msg_size;
    attr.mq_curmsgs = 0;

    memcpy(ret->buff, path, name_size);
    memcpy(ret->buff + name_size, "_res", 5);
    ret->res = mq_open(ret->buff, O_CREAT | O_WRONLY | O_EXCL, 0600, &attr);
    if (ret->res == -1) {
        fprintf(stdout, "Cannot create %s : %s\n", ret->buff, strerror(errno));
        fflush(stdout);
        nfb_sv_close(ret, path);
        return NULL;
    }

    return ret;
}


void nfb_sv_close(void * mq_id, const char * path)
{
    nfb_sv_struct_t *data = mq_id;
    int unsigned name_size;

    name_size = strlen(path);
    memcpy(data->buff, path, name_size);

    if (data->req != -1) {
        memcpy(data->buff + name_size, "_req", 5);
        mq_close(data->req);
        mq_unlink(data->buff);
    }

    if (data->res != -1) {
        memcpy(data->buff + name_size, "_res", 5);
        mq_close(data->res);
        mq_unlink(data->buff);
    }

    if (data->buff_size != 0) {
        data->buff_size = 0;
        free(data->buff);
    }
    free(mq_id);
}

int nfb_sv_cmd_get(void * id, unsigned int* cmd, unsigned int* data_size, svLogicVecVal* offset)
{
    nfb_sv_struct_t *data;
    int mq_ret;
    msg_t *msg;

    data = id;
    mq_ret = mq_receive(data->req, (char *) data->buff, data->buff_size, NULL);

    msg = data->buff;
    *cmd       = msg->type;
    *data_size = msg->size;
    offset[0].aval = msg->offset & 0xffffffff;
    offset[0].bval = 0;
    offset[1].aval = (msg->offset >> 32) & 0xffffffff;
    offset[1].bval = 0;

    return (mq_ret > 0);
}

void nfb_sv_data_get(void * id, const svOpenArrayHandle out)
{
    void * ptr;
    int unsigned ptr_size;
    nfb_sv_struct_t *data;

    ptr      = svGetArrayPtr(out);
    ptr_size = svSizeOfArray(out);
    data     = id;

    memcpy(ptr, data->buff + sizeof(msg_t), ptr_size);
}

void nfb_sv_cmd_send(void * id, unsigned int cmd, const svOpenArrayHandle out)
{
    void * ptr;
    int unsigned ptr_size = 0;
    nfb_sv_struct_t *data;
    msg_t *msg;

    data     = id;
    msg      = data->buff;

    if (out != NULL){
        ptr      = svGetArrayPtr(out);
        ptr_size = svSizeOfArray(out);
        memcpy(data->buff + sizeof(msg_t), ptr, ptr_size);
    }

    msg->type = cmd;
    msg->size = ptr_size;
    mq_send(data->res, data->buff, sizeof(msg_t) + ptr_size, 0);
}
