/**
 * \file frl.h
 * \author Jakub Lukac <xlukac09@stud.fit.vutbr.cz>
 * \date 2015-09
 * \brief Header file for the flow rate limiter(FRL) library
 *
 * Copyright (C) 2015 CESNET
 *
 * SPDX-License-Identifier: BSD-3-Clause OR GPL-2.0-or-later
 *
 */

#ifndef FRL_H_
#define FRL_H_

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <errno.h>

/**
 * Data type for one FRL item
 */
typedef struct {
   uint32_t b_limit;
   uint32_t speed;
   uint32_t t_const;
   uint32_t item_addr;
} frl_item_t;

/**
 * MSb of item address is used as Write/Read flag
 */
#define WR_FLAG 0x80000000
#define RD_FLAG 0x7FFFFFFF

/**
 * Address offsets
 */
#define OFFS_BUCKET_LIMIT  0x00000000
#define OFFS_SPEED         0x00000004
#define OFFS_TIME_CONST    0x00000008
#define OFFS_ITEM_ADDR     0x0000000C
#define OFFS_READ_GENS     0x00000010

/**
 * Masks to extract generic params from 32-bit word
 */
#define GEN_ADDR_W      0xFF000000
#define GEN_B_LIM_W     0x00FF0000
#define GEN_SPEED_W     0x0000FF00
#define GEN_CONST_W     0x000000FF

/**
 * Function type shortcuts
 *
 * Each function should return zero on success or negative error value
 */
typedef int (*frl_write_func)(uint32_t offs, uint32_t val, void *device_specific_data);
typedef int (*frl_read_func)(uint32_t offs, uint32_t *val_ptr, void *device_specific_data);

/**
 * Generics read and parse
 */
int frl_read_gens(uint32_t *gens, frl_read_func fn, void *device_specific_data);
int frl_get_gen(uint32_t g_mask, uint32_t gens);

/**
 * Set speed limit, covert speed \a s [kBps] to item values and write them
 */
double frl_set_limit(uint32_t s, uint32_t b_l, uint32_t addr, frl_write_func fn_w, frl_read_func fn_r, void *device_specific_data);

/**
 * Read item values and covert them to speed limit [kBps]
 */
double frl_read_limit(uint32_t addr, uint32_t *r_b_l, frl_write_func fn_w, frl_read_func fn_r, void *device_specific_data);

/**
 * Convert speed limit [kBps] to item parts \a speed and \a t_const
 */
int frl_spdconv(uint32_t s, uint32_t max_s, uint32_t max_t_c, uint32_t *r_speed, uint32_t *r_t_const);

/**
 * Convert item parts \a speed and \a t_const to speed limit [kBps]
 */
double frl_itmconv(uint32_t speed, uint32_t t_const);

/**
 * Turn off FRL for specific flow
 */
int frl_turnoff(uint32_t addr, frl_write_func fn_w, frl_read_func fn_r, void *device_specific_data);

/* Private section - please use functions above */

/**
 * Write/read item values
 */
int frl_write(frl_item_t *i, frl_write_func fn_w, frl_read_func fn_r, void *device_specific_data);
int frl_read(uint32_t addr, frl_item_t *i, frl_write_func fn_w, frl_read_func fn_r, void *device_specific_data);

/**
 * Rational approximation
 */
int rat(double x, uint32_t max_num, uint32_t max_denom, uint32_t *r_num, uint32_t *r_denom);

#endif
