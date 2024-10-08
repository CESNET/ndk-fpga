/**
 * \file frl_write.c
 * \author Jakub Lukac <xlukac09@stud.fit.vutbr.cz>
 * \date 2015-09
 *
 * Copyright (C) 2015 CESNET
 */

#include "frl.h"

/**
 * \brief Write FLR item values on address \a addr
 * \param i    Pointer to valid item, which should be written
 * \param fn_w Write function
 * \param fn_r Read function
 * \param device_specific_data Pointer to needed device data
 * \return Zero on success
 * \retval err Zero on success or negative error value
 */
int frl_write(frl_item_t *i, frl_write_func fn_w, frl_read_func fn_r, void *device_specific_data)
{
   int err = 0;

   /* check validity of item values */
   uint32_t gens;
   if ((err = frl_read_gens(&gens, fn_r, device_specific_data)) != 0) {
      return err;
   }
   if (i->b_limit   >= pow(2, frl_get_gen(GEN_B_LIM_W, gens)) ||
       i->speed     >= pow(2, frl_get_gen(GEN_SPEED_W, gens)) ||
       i->t_const   >= pow(2, frl_get_gen(GEN_CONST_W, gens)) ||
       i->item_addr >= pow(2, frl_get_gen(GEN_ADDR_W, gens))) {
      errno = EINVAL;
      return -errno;
   }

   /* MSb of writing address has to be '1' */
   uint32_t w_addr = i->item_addr | WR_FLAG;

   if ((err = fn_w(OFFS_BUCKET_LIMIT, i->b_limit, device_specific_data)) != 0) { return err; }
   if ((err = fn_w(OFFS_SPEED,        i->speed,   device_specific_data)) != 0) { return err; }
   if ((err = fn_w(OFFS_TIME_CONST,   i->t_const, device_specific_data)) != 0) { return err; }
   if ((err = fn_w(OFFS_ITEM_ADDR,    w_addr,     device_specific_data)) != 0) { return err; }

   return err;
}
