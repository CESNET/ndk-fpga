/**
 * \file frl_turnoff.c
 * \author Jakub Lukac <xlukac09@stud.fit.vutbr.cz>
 * \date 2015-08
 *
 * Copyright (C) 2015 CESNET
 */

#include "frl.h"

/**
 * \brief Turn off FRL for flow limited by item on address addr
 * \param addr Item address
 * \param fn_w Write function
 * \param fn_r Read function
 * \param device_specific_data Pointer to needed device data
 * \return Zero on success or negative error value, as defined by frl_read or frl_write
 */
int frl_turnoff(uint32_t addr, frl_write_func fn_w, frl_read_func fn_r, void *device_specific_data)
{
   /* item speed value must be zero to turn off FRL */
   frl_item_t tmp_item = {.b_limit = 0, .speed = 0, .t_const = 0, .item_addr = addr};

   return frl_write(&tmp_item, fn_w, fn_r, device_specific_data);
}
