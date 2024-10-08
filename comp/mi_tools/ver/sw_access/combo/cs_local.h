/*!
 * \file cs_local.h:
 *
 * \brief Local (private to library) Combo6 model interface
 *
 * \author Lukas Kekely <kekely@cesnet.cz>
 */
 /*
 * Copyright (C) 2015 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause OR GPL-2.0-or-later
 *
 */

#ifndef _LIBEROUTER_CS_LOCAL_H_
#define _LIBEROUTER_CS_LOCAL_H_

/*!
 * Handle to given device instance.
 */
struct cs_device {
    int              dv_file;
    int              dv_flag;
    u_int32_t        dv_msiz;       /*!< Address window size */
    cs_target_t      dv_bussel;     /*!< Who is on local bus now */
    u_int32_t        dv_id;         /*!< Unique 32-bit design ID */
    u_int32_t        dv_id_hw;      /*!< 32-bit design hardware ID */
    const char       * dv_strid;    /*!< ASCII ID (not unique) */
    unsigned         comps_size;
    cs_component_t   * comps;       /*!< All components */
    const char       * name;        /*!< Design name */

    /* New card identification - CV2 card family */
    char             * dv_board;    /*!< Main board */
//    char           *dv_board_subtype; /*!< Main board subtype */
//    char           *dv_if0_card;    /*!< Addon board in iface connector 0 */
//    char           *dv_if0_chip;    /*!< Chip of addon board */
//    char           *dv_if1_card;    /*!< Addon board in iface connector 1 */
//    char           *dv_if1_chip;    /*!< Chip of addon board */
};

/*!
 * Handle to region of address space for low-level access.
 */
struct cs_space {
    cs_addr_t        sp_base;    /*!< Base offset of space */
    cs_size_t        sp_size;    /*!< Size of mapping */
};

/*!
 * Handle component.
 */
struct cs_component {
    char             name[256];  /*!< ASCII name */
    cs_cidx_t        index;      /*!< index (instance) */
    cs_cver_t        version;    /*!< component version */
    cs_space_t       space;      /*!< space for i/o */
};

#endif /* _LIBEROUTER_CS_LOCAL_H_ */
