/**
 * \file frl_set_limit.c
 * \author Jakub Lukac <xlukac09@stud.fit.vutbr.cz>
 * \date 2015-09
 *
 * Copyright (C) 2015 CESNET
 */

#include "frl.h"

/**
 * \brief Set speed limit
 * \param s    Speed limit [kBps], positive integer or zero
 * \param b_l  Bucket value
 * \param addr Item address
 * \param fn_w Write function
 * \param fn_r Read function
 * \param device_specific_data Pointer to needed device data
 * \retval approx_val Zero on success or positive value of set speed
 * \retval err        Negative error value, as defined by frl_read or frl_write
 *
 * \note
 * Covert speed \a s [kBps] to item values and then write them
 * Speed is set to the best approximation of \a s
 */
double frl_set_limit(uint32_t s, uint32_t b_l, uint32_t addr, frl_write_func fn_w, frl_read_func fn_r, void *device_specific_data)
{
   int err = 0;
   double approx_val = 0.0;

   uint32_t gens;
   if ((err = frl_read_gens(&gens, fn_r, device_specific_data)) != 0) {
      return (double)err;
   }
   uint32_t max_s = pow(2, frl_get_gen(GEN_SPEED_W, gens));
   uint32_t max_t_c = pow(2, frl_get_gen(GEN_CONST_W, gens));
   uint32_t speed;
   uint32_t t_const;

   if ((frl_spdconv(s, max_s, max_t_c, &speed, &t_const)) != 0) {
      approx_val = (double)t_const/speed;
   }

   frl_item_t tmp_item = {.b_limit = b_l, .speed = speed, .t_const = t_const, .item_addr = addr};

   if ((err = frl_write(&tmp_item, fn_w, fn_r, device_specific_data)) != 0) {
      return (double)err;
   }

   return approx_val;
}
