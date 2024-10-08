/**
 * \file frl_get_gen.c
 * \author Jakub Lukac <xlukac09@stud.fit.vutbr.cz>
 * \date 2015-08
 *
 * Copyright (C) 2015 CESNET
 */

#include "frl.h"

/**
 * \brief Parse one of generic parameter from 32-bit word
 * \param g_mask Mask to select generic, one of defined mask
 * \param gens   All generic params as one 32-bit word
 * \retval gen Selected generic parameter on success or -1
 */
int frl_get_gen(uint32_t g_mask, uint32_t gens)
{
   int gen = -1;
   gens &= g_mask;

   switch (g_mask) {
      case GEN_ADDR_W:
         gen = gens >> 24;
         break;
      case GEN_B_LIM_W:
         gen = gens >> 16;
         break;
      case GEN_SPEED_W:
         gen = gens >> 8;
         break;
      case GEN_CONST_W:
         gen = gens;
         break;
   }

   return gen;
}
