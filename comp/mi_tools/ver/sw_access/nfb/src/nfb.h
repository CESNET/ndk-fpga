/*
 *  libnfb - base module header
 *
 *  Copyright (C) CESNET, 2018
 *  Author(s):
 *    Martin Spinler <spinler@cesnet.cz>
 *
 *  SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef NFB_H
#define NFB_H

#include <stdint.h>

#include <nfb/nfb.h>

/*!
 * \brief Structure for the NFB device
 */
struct nfb_device {
	int fd;                         /*!< NFB chardev file descriptor */
	void *fdt;                      /*!< NFB device Device Tree description */
	const char *path;
};


struct nfb_bus;

typedef ssize_t nfb_bus_read_func(const struct nfb_bus *bus, void *buf, size_t nbyte, off_t offset);
typedef ssize_t nfb_bus_write_func(const struct nfb_bus *bus, const void *buf, size_t nbyte, off_t offset);

/*!
 * \brief Structure for the NFB bus
 */
struct nfb_bus {
	const struct nfb_device *dev;   /*!< Bus's device */
	int fdt_offset;                 /*!< Bus's offset in the Device Tree */
	void *priv;                     /*!< Bus's private data */
	int state;			/*!< Bus's state e.g. in case of error */

	nfb_bus_read_func *read;
	nfb_bus_write_func *write;
};


/*!
 * \brief Structure for NFB device component
 */
struct nfb_comp {
	const struct nfb_device *dev;   /*!< Component's device */
	int fdt_offset;                 /*!< Component's offset in the Device Tree */
	struct nfb_bus * bus;           /*!< Component's bus */
	off_t base;                     /*!< Component's offset in the bus address space */
	size_t size;                    /*!< Component's size in the bus address space */
};


//struct nfb_bus *nfb_bus_open_mi(struct nfb_bus *bus);
int nfb_bus_open_mi(struct nfb_bus *bus);
struct nfb_bus *nfb_bus_open(const struct nfb_device *dev, int fdt_offset);

#endif /* NFB_H */
