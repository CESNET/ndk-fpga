/**
 * \file combosix.h
 * \brief Model of the interface to the basic Combo6 operations.
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

#ifndef _LIBEROUTER_COMBOSIX_H_
#define _LIBEROUTER_COMBOSIX_H_

#include <sys/cdefs.h>
#include <sys/types.h>
#include <stdint.h>
#include <stdio.h>

/**
 * Bus size type
 */
typedef u_int32_t cs_size_t;
/**
 * Bus address type
 */
typedef u_int32_t cs_addr_t;

/**
 * Address spaces user may map and access.
 */
typedef enum {
	CS_SPACE_FPGA		= 0,	/**< Combo6, FPGA on bus */
	CS_SPACE_BRIDGE		= 1,	/**< PCI bridge registers */
	CS_SPACE_CPLD		= 2,	/**< Combo6, CPLD on bus */
	CS_SPACE_PLX_EEPROM	= 4,	/**< PLX9054 serial EEPROM */
	CS_SPACE_PCI_CONF	= 5,	/**< PCI configuration space */
	CS_SPACE_NONE		= 3	/**< Invalid space */
} cs_target_t;

#define CS_SPACE_PLX	CS_SPACE_BRIDGE	/**< for compatibility */

/**
 * Handle to given device instance.
 */
typedef struct cs_device cs_device_t;

/**
 * Handle to region of address space for low-level access.
 */
typedef struct cs_space cs_space_t;

/**
 * \defgroup device Device management
 * See the \ref bus page for more details.
 * \{
 */

/**
 * Path to Combo6 character device is OS-dependent. For
 * convenience, provide macro to hide this difference.
 */
#define CS_PATH_DEV(n)		("/dut/" __STRING(n))	/**< get full path to device */
#define CS_PATH_FMTINTDEV	"/dut/%d"		/**< get device filename for given card number (int) */

__BEGIN_DECLS
/*
 * Methods to attach and detach the device.
 */
int cs_attach(cs_device_t **, const char *);
int cs_attach_noex(cs_device_t **, const char *);
int cs_attach_wait(cs_device_t **dev, const char *path, unsigned int timeout);
void cs_detach(cs_device_t **);

/*
 * ... and child drivers.
 */
int cs_children_attach(cs_device_t *);
int cs_children_detach(cs_device_t *);

/*
 * firmware switching
 */
int cs_firmware_switch(const char *, int);
int cs_firmware_get(cs_device_t *);

/*
 * lowlevel network interface routines
 */
int cs_netdev(const char *, int *, int *);

/*
 * card identification
 */
int cs_identify(cs_device_t *, char **, char **, char **);
int cs_identify_cv2(cs_device_t *, char **, char **, char **, char **, char **,
	char **);

/*
 * device tree, fdt
 */
void* cs_fdt(cs_device_t *);

__END_DECLS

/** \} *//* Device management */

/**
 * \defgroup mmap Address region management
 * \ingroup device
 * See the \ref bus page for more details.
 * \{
 */

/**
 * Use this as 'size' to make cs_space_map() map whole address space.
 */
#define CS_MAP_ALL		((cs_size_t)0)

/**
 * This flag to cs_space_map() enforces ioctl() access to given region
 * (by default, memory mapped access is used).
 */
#define CS_MAP_INDIRECT		0x01

__BEGIN_DECLS
int cs_space_map(cs_device_t *, cs_space_t **, cs_target_t, cs_size_t,
	cs_addr_t, u_int32_t);
void cs_space_unmap(cs_device_t * ATTRIBUTE_UNUSED, cs_space_t **);
cs_addr_t cs_space_base_addr(cs_space_t *);
const char *cs_space_name(cs_target_t t);
__END_DECLS

/** \} *//* Address region management */

/**
 * \defgroup access Lowlevel access methods
 * \ingroup device
 * See the \ref bus page for more details.
 * \{
 */

__BEGIN_DECLS
void cs_space_write_4(cs_device_t *, cs_space_t *, cs_addr_t, u_int32_t);
u_int32_t cs_space_read_4(cs_device_t *, cs_space_t *, cs_addr_t);

void cs_space_write_multi_4(cs_device_t *, cs_space_t *, cs_addr_t, cs_size_t,
	u_int32_t *);
void cs_space_read_multi_4(cs_device_t *, cs_space_t *, cs_addr_t, cs_size_t,
	u_int32_t *);
__END_DECLS

/** \} *//* Lowlevel access methods */

/**
 * \defgroup phys Physical mapping of userland memory
 * See the \ref phys page for more details.
 * \{
 */

/**
 * Physical mapping of userland memory - scatter-gather unit.
 */
typedef struct {
	cs_addr_t	sg_addr;	/**< SG address */
	cs_size_t	sg_size;	/**< SG size */
} cs_seg_t;

/**
 * Physical mapping of userland memory - main structure.
 */
typedef struct {
	u_int8_t	*p_data;	/**< phys data? */
	u_int32_t	p_size;		/**< phys size? */
	u_int32_t	p_nseg;		/**< phys nseg? */
	cs_seg_t	*p_segs;	/**< phys segs? */
} cs_phys_t;

__BEGIN_DECLS
int cs_phys_alloc(cs_device_t *, size_t, cs_phys_t **);
int cs_phys_sync_before(cs_device_t *, cs_phys_t *);
int cs_phys_sync_after(cs_device_t *, cs_phys_t *);
int cs_phys_free(cs_device_t *, cs_phys_t **);
__END_DECLS

/** \} *//* Physical mapping of userland memory */

/**
 * \defgroup boot Combo6 boot support
 * See the \ref boot page for more details.
 * \{
 */

/**
 * Boot v1 type.
 */
typedef struct cs_boot_v1 cs_boot_v1_t;

/** Boot v1 structure */
struct cs_boot_v1 {
	u_int32_t	addr;	/**< FPGA address */
	u_int8_t	*data;	/**< FPGA programming data */
	u_int32_t	size;	/**< size of FPGA data in bytes */
	cs_boot_v1_t	*next;	/**< next FPGA */
};

/** Boot v1 types */
enum cs_boot_v1_type {
	CS_BOOT_V1_STANDARD,	/**< standard boot procedure */
};

__BEGIN_DECLS
const char *cs_hw_mchip(cs_device_t *);
char *cs_hw_id(cs_device_t *);

int cs_boot_v1(cs_device_t *, enum cs_boot_v1_type, cs_boot_v1_t *);
int cs_load_pcippc(const char *, cs_boot_v1_t **);
void cs_free_pcippc(cs_boot_v1_t **);
__END_DECLS

/** \} *//* Combo6 boot */

/**
 * \defgroup design Design management
 * See the \ref design page for more details.
 * \{
 */

/**
 * Design load methods
 */
typedef enum {
	CS_DESIGN_NONE	= 0,	/**< reinit of spaces only - no load; arg is NULL */
	CS_DESIGN_MCS	= 1,	/**< arg is 'cs_design_mcs_t *' */
	CS_DESIGN_XML	= 2	/**< arg is 'char *' */
} cs_design_t;

/**
 * Maximum number of designs in #cs_design_mcs_t structure
 */
#define CS_MCS_SIZE	8

/**
 * cs_design_load() structure when #CS_DESIGN_MCS type is selected.
 */
typedef struct cs_design_mcs {
	u_int32_t	unused;
	struct {
		u_int32_t	addr;		/**< FPGA address (0 = master, 8 = addon1, 9 = addon2) */
		const char	*filename;	/**< .mcs filename (or NULL -> terminate) */
	} mcs[CS_MCS_SIZE];			/**< mcs container */
} cs_design_mcs_t;

/** Dummy type for design data */
typedef void cs_design_data_t;

__BEGIN_DECLS
int cs_design_present(cs_device_t *);
int cs_design_load(cs_device_t *, cs_design_t, const cs_design_data_t *);
int cs_design_reload(cs_device_t *, cs_design_t, const cs_design_data_t *);
int cs_design_free(cs_device_t *);
char *cs_design_id(cs_device_t *);
void cs_design_dump(cs_device_t *);
__END_DECLS

/** \} *//* Design management */

/**
 * \defgroup components Component drivers
 * \ingroup design
 * See the \ref design page for more details.
 * \{
 */

/**
 * Component structure
 */
typedef struct cs_component cs_component_t;

/**
 * Component index
 */
typedef u_int32_t cs_cidx_t;

/**
 * Component version
 */
typedef u_int32_t cs_cver_t;

/*!
 * Basic component information
 */
typedef struct cs_component_info {
	char		*name;		/*!< ASCII name */
	cs_cidx_t	index;		/*!< index (instance) */
} cs_component_info_t;

/**
 * Combine component major and minor version to 32-bit word
 */
#define CS_CVER(major, minor)	(((((cs_cver_t)(major))&0xffff) << 16)|((minor)&0xffff))

/**
 * Extract component major version from 32-bit word
 */
#define CS_CVER_MAJOR(version)	(((version)>>16)&0xffff)

/**
 * Extract component minor version from 32-bit word
 */
#define CS_CVER_MINOR(version)	((version)&0xffff)

__BEGIN_DECLS
int cs_component_alloc(cs_device_t * ATTRIBUTE_UNUSED, cs_component_t **,
	const char *, cs_cidx_t, cs_cver_t, cs_space_t *);
int cs_component_free(cs_device_t *, cs_component_t **);
int cs_component_append(cs_device_t *, cs_component_t *, cs_component_t *);
int cs_component_remove(cs_device_t *, cs_component_t **);

int cs_component_for_subtree(cs_device_t *, cs_component_t *,
	int (*)(cs_device_t *, cs_component_t *, const void *), const void *);
int cs_component_for_all(cs_device_t *,
	int (*)(cs_device_t *, cs_component_t *, const void *), const void *);

cs_cver_t cs_component_version(cs_component_t *);
int cs_component_find(cs_device_t *, cs_component_t **, cs_component_t *,
	const char *, cs_cidx_t);
int cs_component_find_space(cs_device_t *, cs_component_t *,
	cs_component_info_t *, cs_space_t **);
int cs_component_find_space_multiple(cs_device_t *, cs_component_t *,
	cs_component_info_t *, cs_space_t **, u_int32_t);
int cs_component_sfind(cs_device_t *, cs_component_t **, const char *id);
int cs_component_space(cs_component_t *, cs_space_t **);
int cs_component_number(cs_device_t *, cs_component_t *, const char *, unsigned int*);

int cs_component_upriv_set(cs_component_t *, void *, void (*)(void *));
void *cs_component_upriv_get(cs_component_t *);
__END_DECLS

/** \} *//* components */

/**
 * \defgroup utils Utilities
 * See the \ref utils page for more details.
 * \{
 */

/**
 * Type of the required libcombo's lock. The values are used to set a mask!
 */
#define CS_LOCK_I2C  1
#define CS_LOCK_MDIO 2
#define CS_LOCK_IBUF 4
#define CS_LOCK_OBUF 8

__BEGIN_DECLS
int cs_mcs_decode(FILE *, u_int8_t **, u_int32_t *);
int cs_lock(int lock_type);
int cs_unlock(int lock_type);
void cs_unlock_all(void);
__END_DECLS

/** \} *//* Utilities */

/**
 * \defgroup xml XML parsing
 * \ingroup utils
 * See the \ref xml page for more details.
 * \{
 */

/**
 * XML file structure
 */
typedef struct cs_xml cs_xml_t;
/**
 * XML tag structure
 */
typedef struct cs_xml_tag cs_xml_tag_t;

__BEGIN_DECLS
int cs_xml_open(cs_xml_t **, cs_xml_tag_t **, const char *);
int cs_xml_close(cs_xml_t **);
void cs_xml_dump(cs_xml_t *, cs_xml_tag_t *, int);

cs_xml_tag_t *cs_xml_tag_child(cs_xml_tag_t *);
cs_xml_tag_t *cs_xml_tag_parent(cs_xml_tag_t *);
cs_xml_tag_t *cs_xml_tag_next(cs_xml_tag_t *);
int cs_xml_tag_find(cs_xml_tag_t *, cs_xml_tag_t **, const char *, int);
int cs_xml_tag_name(cs_xml_tag_t *, const char **, size_t *);
int cs_xml_tag_attr(cs_xml_tag_t *, const char **, size_t *, const char *);
int cs_xml_tag_body(cs_xml_tag_t *, const char **, size_t *);

int cs_xml_name_match(cs_xml_tag_t *, const char *);
int cs_xml_attr_match(cs_xml_tag_t *, const char *, const char *);
int cs_xml_is_version(cs_xml_t *, const char *);
int cs_xml_is_encoding(cs_xml_t *, const char *);

int cs_xml_get_uint32(u_int32_t *, const char *, size_t);
int cs_xml_get_string(char **, const char *, size_t);
__END_DECLS

/** \} *//* XML parsing */

/**
 * \defgroup ptm PTM card I/O
 * See the \ref ptm page for more details.
 * \{
 */

#define CS_PTM_OP_INC	0	/**< operation with INC registers */
#define CS_PTM_OP_RT	1	/**< operation with RT registers */
#define CS_PTM_OP_TS	2	/**< operation with TS registers */
#define CS_PTM_OP_PS	3	/**< operation with PS registers */

/**
 * PTM i/o structure
 */
typedef struct {
	u_int32_t	op;		/**< #CS_PTM_OP_INC etc.. */
	u_int32_t	regs[3];	/**< PTM register contents */
} cs_ptm_t;

__BEGIN_DECLS
int cs_ptm_read(cs_device_t *, cs_ptm_t *);
int cs_ptm_write(cs_device_t *, cs_ptm_t *);
__END_DECLS

/** \} *//* PTM card i/o */

#endif /* _LIBEROUTER_COMBOSIX_H_ */
