/**
 * \file frl_itmconv.c
 * \author Jakub Lukac <xlukac09@stud.fit.vutbr.cz>
 * \date 2015-08
 *
 * Copyright (C) 2015 CESNET
 */

#include "frl.h"

/**
 * \brief Convert item speed and t_const to speed limit [kBps]
 * \param speed   Item speed value
 * \param t_const Item time constant value
 * \return Speed limit in [kBps] or INFINITY when FRL is turned off
 */
double frl_itmconv(uint32_t speed, uint32_t t_const)
{
   if (speed == 0) {
      return INFINITY;  /* FRL is turned off */
   }
   else {
      return ((double)t_const/speed) * 1000000;
   }
}
