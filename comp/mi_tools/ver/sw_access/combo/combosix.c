/**
 * \file combosix.c
 * \brief Model of the basic Combo6 operations.
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2015
 */
 /*
 * Copyright (C) 2015 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause OR GPL-2.0-or-later
 *
 */

#include "combosix.h"
#include "cs_local.h"
#include "../dpi_sw_access.h"

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

/**
 * \brief Open combo6 device
 * \param d Returned device structure
 * \param path Path for device (see #CS_PATH_DEV)
 * \return zero on success or a negative error code
 *
 * Initialize device abstraction structure, opening device file
 * given by \a path for (non-)exclusive access.
 */
static int cs_attach_real(cs_device_t **d, const char *path, int mode) {
    dpi_device_info cfg;

    *d = (cs_device_t*)malloc(sizeof(**d));
    if (*d == NULL)
        return -ENOMEM;

    (*d)->dv_file = path[strlen(path)-1]-'0';
    if(dpiinfo((*d)->dv_file,&cfg)) {
        free(*d);
        *d = NULL;
        return -ENOENT;
    }

    (*d)->dv_flag = 0;
    (*d)->comps_size = 0;
    (*d)->comps = NULL;
    (*d)->dv_bussel = CS_SPACE_NONE;
    (*d)->dv_msiz = cfg.memory_size;

    /* Hardware identification */
    (*d)->dv_board = malloc(strlen(cfg.board_name)+1);
    if((*d)->dv_board == NULL)
        return -ENOMEM;
    memcpy((*d)->dv_board, cfg.board_name, strlen(cfg.board_name)+1);
/*  (*d)->dv_board_subtype = strdup(cfg.ci_board_subtype);
    (*d)->dv_if0_card = strdup(cfg.ci_addon[0].card);
    (*d)->dv_if0_chip = strdup(cfg.ci_addon[0].chip);
    (*d)->dv_if1_card = strdup(cfg.ci_addon[1].card);
    (*d)->dv_if1_chip = strdup(cfg.ci_addon[1].chip);*/

    (*d)->name = cfg.design_name;
    (*d)->dv_id = cfg.design_id;
    (*d)->dv_id_hw = cfg.design_hw_id;
    (*d)->dv_strid = cfg.design_name;

    return 0;
}

/**
 * \brief Close the combo6 device
 * \param d Combo6 device structure
 *
 * Close the device and invalidate any resources allocated. If there is a design
 * loaded, free it as well.
 */
void cs_detach(cs_device_t **d) {
    cs_design_free(*d);
    free((*d)->dv_board);
    free(*d);
    *d = NULL;
}

int cs_attach(cs_device_t **d, const char *path) {
    return cs_attach_real(d, path, 0xdeadbeef);
}
int cs_attach_noex(cs_device_t **d, const char *path) {
    return cs_attach_real(d, path, 0xdeadbeef);
}
int cs_attach_wait(cs_device_t **d, const char *path, unsigned int timeout) {
    return cs_attach(d, path);
}



/**
 * \brief Free all components associated to active design
 * \param d Combo6 device structure
 * \return zero on success otherwise a negative error code
 */
int cs_design_free(cs_device_t *d) {
    if(d->comps) free(d->comps);
    d->comps = NULL;
    d->comps_size = 0;
    return 0;
}

/**
 * \brief Test if design is active inside hardware
 * \param d Combo6 device name
 * \retval zero design is not present and has to be loaded
 * \retval one design is present
 * \retval negative error code
 */
int cs_design_present(cs_device_t *d) {
    return (d->dv_id != 0);
}

/**
 * \brief Load design
 * \param d Combo6 device name
 * \param filename Path to the XML file
 * \param reprogram Whether to boot processed design or not
 * \return zero on success or a negative error code
 */
static int cs_design_load_xml(cs_device_t *d, const char *filename, int reprogram) {
    dpi_device_component_info ci;
    cs_design_free(d);
    while(dpicomponent(d->dv_file, d->comps_size, &ci) == 0)
        d->comps_size++;
    d->comps = malloc(sizeof(cs_component_t)*d->comps_size);
    if(!d->comps)
        return -ENOMEM;
    for(unsigned i=0; i<d->comps_size; i++) {
        dpicomponent(d->dv_file, i, &ci);
        memcpy(d->comps[i].name, ci.name, strlen(ci.name)+1);
        d->comps[i].index = ci.index;
        d->comps[i].version = ci.version;
        d->comps[i].space.sp_base = ci.space_base;
        d->comps[i].space.sp_size = ci.space_size;
    }
    return 0;
}

int cs_design_load(cs_device_t *d, cs_design_t type, const cs_design_data_t *arg) {
    return cs_design_load_xml(d, NULL, 0xdeadbeef);
}

int cs_design_reload(cs_device_t *d, cs_design_t type, const cs_design_data_t *arg) {
    return cs_design_load_xml(d, NULL, 0xdeadbeef);
}



/**
 * \brief Find a space inside active design
 * \param d Combo6 device structure
 * \param result Returned component
 * \param parent Parent component or NULL (root space)
 * \param name Component name in ASCII
 * \param index Component index (from zero)
 * \return zero on success otherwise a negative error code
 */
int cs_component_find(cs_device_t *d, cs_component_t **result, cs_component_t *parent, const char *name, cs_cidx_t index) {
    for(unsigned i=0; i<d->comps_size; i++)
        if (d->comps[i].name && !strcmp(d->comps[i].name, name) && d->comps[i].index == index) {
            *result = d->comps+i;
            return 0;
        }
    return -ENOENT;
}

/**
 * \brief Get component space
 * \param c Component structure
 * \param space Returned assigned space
 * \return zero on success otherwise a negative error code
 */
int cs_component_space(cs_component_t *c, cs_space_t **space) {
    *space = &(c->space);
    return 0;
}

/**
 * \brief Find a component space inside active design
 * \param d Combo6 device structure
 * \param parent Parent component or NULL (root space)
 * \param cinfo Basic component information used as a search key
 * \param result Returned space
 * \return zero on success otherwise a negative error code
 */
int cs_component_find_space(cs_device_t *d, cs_component_t *parent, cs_component_info_t *cinfo, cs_space_t **result) {
    int xerr;
    cs_component_t *comp;

    xerr = cs_component_find(d, &comp, parent, cinfo->name, cinfo->index);
    if (xerr >= 0)
        xerr = cs_component_space(comp, result);

    return xerr;
}

/**
 * \brief Map an address region
 * \param d Combo6 device structure
 * \param s Returned allocated space structure
 * \param type Target type
 * \param size Region size in bytes
 * \param offs Absolute region offset in bytes
 * \param flag Mapping options
 * \return zero on success or a negative error code
 *
 * Map portion of device address space denoted by \a type beginning at offset
 * \a offs covering \a size bytes. If the \a size argument equals #CS_MAP_ALL,
 * whole address space beginning at given offset is mapped. Returns zero on
 * success. The \a flag argument may be a bitwise OR of:
 *
 * - #CS_MAP_INDIRECT
 *	- The region will be accessed using ioctl() syscall. By default,
 *	  regions are accessed using direct memory mapping, if possible,
 *	  which is significantly faster.
 *
 * If \a flag is zero, default options are used.
 */
int cs_space_map(cs_device_t *d, cs_space_t **s, cs_target_t type, cs_size_t size, cs_addr_t offs, u_int32_t flag) {
    *s = (cs_space_t*)malloc(sizeof(**s));
    if (*s == NULL)
        return -ENOMEM;

    (*s)->sp_base = offs;
    (*s)->sp_size = (size == CS_MAP_ALL) ? (d->dv_msiz - offs) : size;

    return 0;
}

/**
 * \brief Unmap an address space region
 * \param d Combo6 device structure
 * \param s Space structure
 *
 * Invalidate the space abstraction object and release any associated
 * resources.
 */
void cs_space_unmap(cs_device_t *d, cs_space_t **s) {
    free(*s);
    *s = NULL;
}

void *cs_component_upriv_get(cs_component_t *c) {
    return NULL;
}

/**
 * \brief Get component version
 * \param c Component structure
 * \return Component version (see #CS_CVER_MAJOR and #CS_CVER_MINOR macros)
 */
u_int32_t cs_component_version(cs_component_t *c) {
    return c->version;
}

/**
 * \brief Get number of components with specified name
 * \param d Combo6 device structure
 * \param parent Parent component or NULL (root space)
 * \param name Component name
 * \param number Number of founded components
 * \return zero on success otherwise a negative error code
 */
int cs_component_number(cs_device_t *d, cs_component_t *parent, const char *name, unsigned int *number) {
    *number = 0;
    for(unsigned i=0; i<d->comps_size; i++) {
        if (d->comps[i].name && !strcmp(d->comps[i].name, name))
            (*number)++;
    }
    return 0;
}



/**
 * \brief Read four bytes (32-bit word) from bus
 * \param d Combo6 device structure
 * \param s Space structure
 * \param offs Relative offset into space structure in bytes
 * \retval Read 32-bit word
 *
 * Read a single 32-bit value from offset \a offs relative to space region \a s.
 */
u_int32_t cs_space_read_4(cs_device_t *d, cs_space_t *s, cs_addr_t offs) {
    unsigned int value;
    dpiread(d->dv_file, s->sp_base+offs, &value);
    return value;
}

/**
 * \brief Read an array of four byte (32-bit word) units from bus
 * \param d Combo6 device structure
 * \param s Space structure
 * \param offs Relative offset into space structure in bytes
 * \param count Number of 32-bit words to read
 * \param buf Array for read 32-bit words
 *
 * Read \a count 32-bit values from space region \a s beginning at offset
 * \a offs and store them to \a buf. Offset must be aligned at 32 bits.
 */
void cs_space_read_multi_4(cs_device_t *d, cs_space_t *s, cs_addr_t offs, cs_size_t count, u_int32_t *buf) {
    for(unsigned i=0; i<count; i++)
        dpiread(d->dv_file, s->sp_base+offs+(i<<2), buf+i);
}

/**
 * \brief Write four bytes (32-bit word) to bus
 * \param d Combo6 device structure
 * \param s Space structure
 * \param offs Relative offset into space structure in bytes
 * \param val 32-bit word to write
 *
 * Write value \a val at offset \a offs relative to beginning of space region
 * \a s with a single 32-bit bus cycle. Offset must be aligned at 32 bits.
 */
void cs_space_write_4(cs_device_t *d, cs_space_t *s, cs_addr_t offs, u_int32_t val) {
    dpiwrite(d->dv_file, s->sp_base+offs, val);
}

/**
 * \brief Write an array of four byte (32-bit word) units to bus
 * \param d Combo6 device structure
 * \param s Space structure
 * \param offs Relative offset into space structure in bytes
 * \param count Number of 32-bit words to write
 * \param buf Array of 32-bit words to write
 *
 * Write \a count 32-bit values stored in \a buf to space region \a s beginning
 * at offset \a offs. Offset must be aligned at 32 bits.
 */
void cs_space_write_multi_4(cs_device_t *d, cs_space_t *s, cs_addr_t offs, cs_size_t count, u_int32_t *buf) {
    for(unsigned i=0; i<count; i++)
        dpiwrite(d->dv_file, s->sp_base+offs+(i<<2), buf[i]);
}




/**
 * Check if \a parm and \a name are not NULL and then assign \a name to \a parm.
 */
#define frob(parm, name)\
do {\
    if ((name) == NULL) {\
        ret = -ENXIO;\
    } else {\
        if ((parm) != NULL)\
            *(parm) = (name);\
    }\
} while (0)
/**
 * \brief Describe the main board, addon card & chip of given device instance
 * \param dev Device handle
 * \param board Filled with static name of main board if not NULL
 * \param card Filled with static name of addon card if not NULL
 * \param chip Filled with static name of addon chip if not NULL
 * \retval zero on success,
 * \retval negative error code, as defined by errno(2)
 *
 * \note
 * This function is obsolete - do not use it anymore. Here is still only
 * because of backward compatibility.
 */
int cs_identify(cs_device_t *dev, char **board, char **card, char **chip) {
    int ret = 0;

    frob(board, dev->dv_board);
    frob(card, NULL);
    frob(chip, NULL);

    return ret;
}




int cs_lock(int lock_type) {
    printf("warning: cs_lock not implemented\n");
    return 0;
}
int cs_unlock(int lock_type) {
    printf("warning: cs_unlock not implemented\n");
    return 0;
}
void cs_unlock_all(void) {
    printf("warning: cs_unlock_all not implemented\n");
}


/*
 * device tree, fdt
 */
void* cs_fdt(cs_device_t *d){
    FILE* f;
    long byteCnt;
    size_t rSize;
    void *buffer;

    /* Read the device tree blob from a file */
    f = fopen("./DeviceTree-dut0.dtb","r");
    if(!f) {
        perror("Unable to open the device tree blob! \n");
        return NULL;
    }
    /* Allocate the required byte array */
    fseek(f,0L,SEEK_END);
    byteCnt = ftell(f);
    rewind(f);

    /* Allocate the memory */
    buffer = malloc(byteCnt);
    if(buffer == NULL) {
        printf("Unable to allocate memory for device tree!\n");
        return NULL;
    }

    /* Read data to allocated memory */
    rSize = fread(buffer,1,byteCnt,f);
    if(rSize == 0 || rSize < byteCnt) {
        perror("Error during read operation: ");
        fclose(f);
        free(buffer);
        return NULL;
    }

    /* Close the file structure (everything is already in buffer)  */
    fclose(f);

    return buffer;
}
