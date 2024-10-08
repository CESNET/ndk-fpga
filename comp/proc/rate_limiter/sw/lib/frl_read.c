/**
 * \file frl_read.c
 * \author Jakub Lukac <xlukac09@stud.fit.vutbr.cz>
 * \date 2015-09
 *
 * Copyright (C) 2015 CESNET
 */

#include "frl.h"

/**
 * \brief Read FLR item values from address \a addr
 * \param addr Item address
 * \param i    Reference to an item type, whose values are set by the function
 * \param fn_w Write function
 * \param fn_r Read function
 * \param device_specific_data Pointer to needed device data
 * \retval err Zero on success or negative error value
 */
int frl_read(uint32_t addr, frl_item_t *i, frl_write_func fn_w, frl_read_func fn_r, void *device_specific_data)
{
   int err = 0;

   /* check validity of addr */
   uint32_t gens;
   if ((err = frl_read_gens(&gens, fn_r, device_specific_data)) != 0) {
      return err;
   }
   if (addr >= pow(2, frl_get_gen(GEN_ADDR_W, gens))) {
      errno = EINVAL;
      return -errno;
   }

   /* MSb of reading item address has to be '0' */
   uint32_t r_addr = addr & RD_FLAG;

   /* prepare item values on address addr to reading */
   if ((err = fn_w(OFFS_ITEM_ADDR, r_addr, device_specific_data)) != 0) { return err; }
   /* read each value */
   uint32_t b_l, s, t_c;
   if ((err = fn_r(OFFS_BUCKET_LIMIT, &b_l, device_specific_data)) != 0) { return err; }
   if ((err = fn_r(OFFS_SPEED,        &s,   device_specific_data)) != 0) { return err; }
   if ((err = fn_r(OFFS_TIME_CONST,   &t_c, device_specific_data)) != 0) { return err; }

   /* store read values */
   i->b_limit   = b_l;
   i->speed     = s;
   i->t_const   = t_c;
   i->item_addr = addr;

   return err;
}
