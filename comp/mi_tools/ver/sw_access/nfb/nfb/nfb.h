/*
 *  libnfb public header file for verification - NFB module
 *
 *  Copyright (C) CESNET, 2018
 *  Author(s):
 *    Lukas Kekely <kekely@cesnet.cz>
 *
 *  SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef LIBNFB_H
#define LIBNFB_H

#include <stdint.h>
#include <stddef.h>
#include <unistd.h>
#include <errno.h>

#include "fdt.h"


/* ~~~~[ DEFINES ]~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

#define NFB_PATH_DEV(n)      ("DeviceTree-dut" __STRING(n) ".dtb")
#define NFB_DEFAULT_DEV_PATH ("DeviceTree-dut0.dtb")

/* ~~~~[ TYPES ]~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

/*!
 * \brief struct nfb_device  Opaque NFB device datatype
 */
struct nfb_device;

/*!
 * \brief struct nfb_comp  Opaque NFB component datatype
 */
struct nfb_comp;


/* ~~~~[ PROTOTYPES ]~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

/* ~~~~[ DEVICE ] ~~~~ */
/*!
 * \brief   Open the NFB device
 * \param[in]   path  Path to the NFB device file
 * \return
 *     - NFB device handle on success
 *     - NULL on error (errno is set)
 *
 * This is the initialization function, which must be called before other
 * library functions. Upon successful completion, the returned value is a NFB
 * device handle to be passed to other functions.
 */
struct nfb_device *nfb_open(const char *path);

/*!
 * \brief   Close the NFB device
 * \param[in]  dev  NFB device handle
 *
 * Call this function to trminate working with NFB device and cleanup. Handle
 * passed to this function can not be used further.
 */
void nfb_close(struct nfb_device *dev);

/*!
 * \brief nfb_get_fdt  Retrieve NFB device Device Tree description
 * \param[in] dev  NFB device handle
 * \return
 *   - Device Tree (in FDT format) on success
 *   - NULL on error
 */
const void *nfb_get_fdt(const struct nfb_device *dev);

/*!
 * \brief nfb_comp_count  Return count of components present in firmware
 * \param[in] dev         NFB device handle
 * \param[in] compatible  Component 'compatible' string
 * \return
 *   - Non-negative number of components on success
 *   - Negative error code on error
 */
int nfb_comp_count(const struct nfb_device *dev, const char *compatible);

/*!
 * \brief nfb_comp_find   Return FDT offset of a specific component
 * \param[in] dev         NFB device handle
 * \param[in] compatible  Component 'compatible' string
 * \param[in] index       Component index
 * \return
 *   - Non-negative FDT offset of the component on success
 *   - Negative error code on error
 */
int nfb_comp_find(const struct nfb_device *dev, const char *compatible, unsigned index);

/* ~~~~[ COMPONENTS ]~~~~ */

/*!
 * \brief Get component from the user data pointer
 * \param[in] ptr         User data pointer
 * \return
 *    Component handle
 *
 * This function doesn't check validity of input pointer.
 */
struct nfb_comp *nfb_user_to_comp(void *ptr);

/*!
 * \brief Get pointer to the user data space allocated in \ref nfb_comp_open_ext
 * \param[in] comp        Component handle
 * \return
 *    Pointer to user data space
 */
void *nfb_comp_to_user(struct nfb_comp *comp);

/*!
 * \brief Open component specified by \p offset
 * \param[in] dev         NFB device handle
 * \param[in] fdt_offset  FDT offset of the component
 * \return
 *   - Component handle on success
 *   - NULL on error (errno is set)
 */
struct nfb_comp *nfb_comp_open(const struct nfb_device *dev, int fdt_offset);

/*!
 * \brief Open component specified by \p offset
 * \param[in] dev         NFB device handle
 * \param[in] fdt_offset  FDT offset of the component
 * \param[in] user_size   Size of user space allocated in component
 * \return
 *   - Component handle on success
 *   - NULL on error (errno is set)
 */
struct nfb_comp *nfb_comp_open_ext(const struct nfb_device *dev, int fdt_offset, int user_size);

/*!
 * \brief nfb_comp_close  Close component
 * \param[in] component  Component handle
 *
 * Call this function when your work with the component is finished. After it
 * returns, the component handle must not be used again.
 *
 * \note Closes raw components too
 */
void nfb_comp_close(struct nfb_comp *component);

/*!
 * \brief nfb_comp_lock  Lock a component
 * \param[in] component  Component handle
 * \return
 *   - 1 on successful lock
 *   - 0 on unsuccessful lock
 *   - I am not sure about signalling errors here
 *
 * When a component is locked, no other lock() to the same component shall
 * succeed before the component is unlocked again. To make this work, locking
 * should be enforced by the driver.
 *
 * The expected usage is:
 * ~~~~~~~~~~~~~~~~~~~~~~~
 * if (nfb_comp_lock(component)) {
 *   // safe to assume no-one else has locked the component
 *   ...
 *   nfb_comp_unlock(component);
 * }
 * ~~~~~~~~~~~~~~~~~~~~~~~
 */
int nfb_comp_lock(const struct nfb_comp *component, uint32_t features);

/*!
 * \brief nfb_comp_unlock  Unlock a component
 * \param[in] component  Component handle
 *
 * \see nfb_comp_lock
 */
void nfb_comp_unlock(const struct nfb_comp *component, uint32_t features);

/*!
 * \brief nfb_comp_read  Read data from specific offset in the component
 * \param[in] comp       Component handle
 * \param[in] buf        Buffer to store the data to
 * \param[in] nbyte      Number of bytes to read
 * \param[in] offset     Offset in the component
 * \return
 *   - The amount of bytes successfully read on success
 *   - Negative error code on error (errno is set)
 *
 * \note See `man 2 pread' on Linux
 */
ssize_t nfb_comp_read(const struct nfb_comp *comp, void *buf, size_t nbyte, off_t offset);

/*!
 * \brief nfb_comp_write  Write data to a specific offset in the component
 * \param[in] comp       Component handle
 * \param[in] buf        Buffer containing the data to be written
 * \param[in] nbyte      Number of bytes to write
 * \param[in] offset     Offset in the component
 * \return
 *   - The amount of bytes successfully written on success
 *   - Negative error code on error (errno is set)
 */
ssize_t nfb_comp_write(const struct nfb_comp *comp, const void *buf, size_t nbyte, off_t offset);

static inline uint8_t nfb_comp_read8(const struct nfb_comp *component, off_t offset) {
	uint8_t value;
	nfb_comp_read(component, &value, sizeof(value), offset);
	return value;
}

static inline uint16_t nfb_comp_read16(const struct nfb_comp *component, off_t offset) {
	uint16_t value;
	nfb_comp_read(component, &value, sizeof(value), offset);
	return value;
}

static inline uint32_t nfb_comp_read32(const struct nfb_comp *component, off_t offset) {
	uint32_t value;
	nfb_comp_read(component, &value, sizeof(value), offset);
	return value;
}

static inline uint64_t nfb_comp_read64(const struct nfb_comp *component, off_t offset) {
	uint64_t value;
	nfb_comp_read(component, &value, sizeof(value), offset);
	return value;
}

static inline void nfb_comp_write8(const struct nfb_comp *component, off_t offset, uint8_t value) {
	nfb_comp_write(component, &value, sizeof(value), offset);
}

static inline void nfb_comp_write16(const struct nfb_comp *component, off_t offset, uint16_t value) {
	nfb_comp_write(component, &value, sizeof(value), offset);
}

static inline void nfb_comp_write32(const struct nfb_comp *component, off_t offset, uint32_t value) {
	nfb_comp_write(component, &value, sizeof(value), offset);
}

static inline void nfb_comp_write64(const struct nfb_comp *component, off_t offset, uint64_t value) {
	nfb_comp_write(component, &value, sizeof(value), offset);
}

//int nfb_comp_get_version(const struct nfb_comp *component);
//int nfb_comp_get_index(const struct nfb_comp *component);

#endif /* LIBNFB_H */
