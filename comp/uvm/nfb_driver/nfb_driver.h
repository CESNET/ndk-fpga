/*
 * file       : nfb_driver.h
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: create interprocess comunication with nfb programs
 * date       : 2022
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


#ifdef __cplusplus
extern "C" {
#endif

#include "svdpi.h"


void * nfb_sv_create(char * addr, int * port);
void   nfb_sv_close(void * mq_id);

int    nfb_sv_set_fdt(void * mq_id, const svOpenArrayHandle out);
void * nfb_sv_cmd_get(void * id, unsigned int* cmd, unsigned int* data_size, svLogicVecVal* offset);
void   nfb_sv_process(void * id, const svOpenArrayHandle out);


#ifdef __cplusplus
}
#endif

