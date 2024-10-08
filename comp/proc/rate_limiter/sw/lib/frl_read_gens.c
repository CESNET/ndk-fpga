/**
 * \file frl_read_gens.c
 * \author Jakub Lukac <xlukac09@stud.fit.vutbr.cz>
 * \date 2015-08
 *
 * Copyright (C) 2015 CESNET
 */

#include "frl.h"

/**
 * \brief Read all generic params from FRL
 * \param gens Reference to an int type, whose value is set by the function
 * \param fn   Read function
 * \param device_specific_data Pointer to needed device data
 * \return Zero on success or negative error value of read function
 */
int frl_read_gens(uint32_t *gens, frl_read_func fn, void *device_specific_data)
{
   return fn(OFFS_READ_GENS, gens, device_specific_data);
}
