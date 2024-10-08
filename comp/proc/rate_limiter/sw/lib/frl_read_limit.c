/**
 * \file frl_read_limit.c
 * \author Jakub Lukac <xlukac09@stud.fit.vutbr.cz>
 * \date 2015-08
 *
 * Copyright (C) 2015 CESNET
 */

#include "frl.h"

/**
 * \brief Read item speed limit
 * \param addr  Item address
 * \param r_b_l Reference to an int type, whose value is set by the function
 * \param fn_w  Write function
 * \param fn_r  Read function
 * \param device_specific_data Pointer to needed device data
 * \retval limit Converted item speed limit [kBps] on success or INFINITY when FRL is turned off
 * \retval err   Negative error value, as defined by frl_read
 *
 * \note
 * BUCKET_LIMIT value is returned as *r_b_l unless *r_b_l is NULL
 */
double frl_read_limit(uint32_t addr, uint32_t *r_b_l, frl_write_func fn_w, frl_read_func fn_r, void *device_specific_data)
{
   int err = 0;
   frl_item_t tmp_item;

   if ((err = frl_read(addr, &tmp_item, fn_w, fn_r, device_specific_data)) != 0) {
      return (double)err;
   }

   if (r_b_l != NULL)
      *r_b_l = tmp_item.b_limit;

   double limit = frl_itmconv(tmp_item.speed, tmp_item.t_const);

   return limit;
}
