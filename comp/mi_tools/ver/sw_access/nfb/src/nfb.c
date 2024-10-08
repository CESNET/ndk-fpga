/*
 *  libnfb - base module
 *
 *  Copyright (C) CESNET, 2018
 *  Author(s):
 *    Martin Spinler <spinler@cesnet.cz>
 *
 *  SPDX-License-Identifier: BSD-3-Clause
 */

#include <errno.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

#include <libfdt.h>
#include <nfb/nfb.h>

#include "nfb.h"
#include "../../dpi_sw_access.h"

//#include "mi.c"

const void *nfb_get_fdt(const struct nfb_device *dev)
{
	return dev->fdt;
}

struct nfb_comp *nfb_user_to_comp(void *ptr)
{
	return ((struct nfb_comp *) ptr) - 1;
}

void *nfb_comp_to_user(struct nfb_comp *ptr)
{
	return (void *)(ptr + 1);
}

struct nfb_device *nfb_open(const char *devname)
{
	off_t size;
	int fd;
	int ret;
	struct nfb_device *dev;

	/* Open device */
	fd = open(devname, O_RDWR, 0);
	if (fd == -1) {
		goto err_open;
	}

	/* Allocate structure */
	dev = (struct nfb_device*) malloc(sizeof(struct nfb_device));
	if (dev == 0) {
		goto err_malloc_dev;
	}

	dev->fd = devname[strlen(devname)-5] - '0';
	dev->path = devname;

	/* Read FDT from driver */
	size = lseek(fd, 0, SEEK_END);
	lseek(fd, 0, SEEK_SET);
	if (size == 0) {
		errno = ENODEV;
		fprintf(stderr, "FDT size is zero\n");
		goto err_fdt_size;
	}
	dev->fdt = malloc(size);
	if (dev->fdt == NULL) {
		goto err_malloc_fdt;
	}
	ret = read(fd, dev->fdt, size);
	if (ret != size) {
		errno = ENODEV;
		goto err_read_fdt;
	}

	/* Check for valid FDT */
	ret = fdt_check_header(dev->fdt);
	if (ret != 0) {
		errno = EBADF;
		goto err_fdt_check_header;
	}

	close(fd);
	return dev;

err_fdt_check_header:
err_read_fdt:
	free(dev->fdt);
err_fdt_size:
err_malloc_fdt:
	free(dev);
err_malloc_dev:
	close(fd);
err_open:
	return NULL;
}

void nfb_close(struct nfb_device *dev)
{
	free(dev->fdt);
	free(dev);
	dev = NULL;
}

int nfb_comp_count(const struct nfb_device *dev, const char *compatible)
{
	if (!dev || !compatible)
		return -1;

	const void *fdt = nfb_get_fdt(dev);
	int node_offset;
	int count = 0;

	for_each_compatible_node(fdt, node_offset, compatible) {
		count++;
	}

	return count;
}

int nfb_comp_find(const struct nfb_device *dev, const char *compatible, unsigned index)
{
	if (!dev || !compatible)
		return -1;

	const void *fdt = nfb_get_fdt(dev);
	int node_offset;
	unsigned count = 0;

	for_each_compatible_node(fdt, node_offset, compatible) {
		if (count == index)
			return node_offset;
		count++;
	}

	return node_offset;
}

int nfb_bus_open_mi(struct nfb_bus *bus);

struct nfb_bus *nfb_bus_open_for_comp(const struct nfb_device *dev, int fdt_offset)
{
	/* TODO*/
	fdt_offset = fdt_node_offset_by_compatible(dev->fdt, -1, "netcope,bus,mi");
	return nfb_bus_open(dev, fdt_offset);
}

struct nfb_bus *nfb_bus_open(const struct nfb_device *dev, int fdt_offset)
{
	int ret;
	struct nfb_bus * bus;

	bus = malloc(sizeof(struct nfb_bus));
	if (bus == NULL) {
		goto err_malloc;
	}

	bus->dev = dev;
	bus->fdt_offset = fdt_offset;

	/*ret = nfb_bus_open_mi(bus);
	if (ret != 0) {
		printf("open MI error, %d\n", ret);
		goto err_bus_open;
	} */

	return bus;

err_bus_open:
	free(bus);
err_malloc:
	return NULL;
}

void nfb_bus_close(struct nfb_bus * bus)
{
	free(bus);
}

struct nfb_comp *nfb_comp_open(const struct nfb_device *dev, int fdt_offset)
{
	return nfb_comp_open_ext(dev, fdt_offset, 0);
}

struct nfb_comp *nfb_comp_open_ext(const struct nfb_device *dev, int fdt_offset, int user_size)
{
	int proplen;
	const fdt32_t *prop;
	struct nfb_comp *comp;

	prop = fdt_getprop(dev->fdt, fdt_offset, "reg", &proplen);
	if (proplen != sizeof(*prop) * 2) {
		errno = EBADFD;
		goto err_fdt_getprop;
	}
	comp = malloc(sizeof(struct nfb_comp) + user_size);
	if (!comp) {
		goto err_malloc;
	}

	comp->dev = dev;
	comp->base = fdt32_to_cpu(prop[0]);
	comp->size = fdt32_to_cpu(prop[1]);
	comp->bus = nfb_bus_open_for_comp(dev, fdt_offset);
	if (comp->bus == NULL) {
		errno = EBADF;
		goto err_bus_open;
	}

	return comp;

err_bus_open:
	free(comp);
err_malloc:
err_fdt_getprop:
	return NULL;
}

void nfb_comp_close(struct nfb_comp *comp)
{
	free(comp);
}

int nfb_comp_lock(const struct nfb_comp *component, uint32_t features)
{
	if (!component)
		return -1;

	// TODO Implement in driver, this is a stub
	//fprintf(stderr, "Component locking is not really implemented!\n");

	return 1;
}

void nfb_comp_unlock(const struct nfb_comp *component, uint32_t features)
{
	if (!component)
		return;

	return;
}

int nfb_comp_get_version(const struct nfb_comp *component)
{
	if (!component)
		return -1;

	int lenp;

	const fdt32_t *prop;
	prop = fdt_getprop(nfb_get_fdt(component->dev),
			component->fdt_offset, "version", &lenp);
	if (lenp != sizeof(*prop))
		return -1;

	return fdt32_to_cpu(*prop);
}

ssize_t nfb_comp_read(const struct nfb_comp *comp, void *buf, size_t nbyte, off_t offset)
{
	if (offset + nbyte > comp->size)
		return -1;
	if ((offset & 3) || (nbyte & 3))
		return -1;
	for(int o=0; o<nbyte; o+=4)
#ifdef NFB_IFC
		dpi_read32(comp->dev->path, comp->base + offset + o, buf+o);
#else
		dpiread(comp->dev->fd, comp->base + offset + o, buf+o);
#endif
	return nbyte;
}

ssize_t nfb_comp_write(const struct nfb_comp *comp, const void *buf, size_t nbyte, off_t offset)
{
	size_t round_nbyte;
	uint32_t last;
	if (offset + nbyte > comp->size)
		return -1;
	if (offset & 3)
		return -1;
	round_nbyte = nbyte & 0xfffffffc;
	for(int o=0; o<round_nbyte; o+=4)
#ifdef NFB_IFC
		dpi_write32(comp->dev->path, comp->base + offset + o, *((uint32_t*)(buf+o)));
#else
		dpiwrite(comp->dev->fd, comp->base + offset + o, *((uint32_t*)(buf+o)));
#endif
	if(round_nbyte < nbyte) {
		last = 0;
		for(int i=round_nbyte; i<nbyte; i++)
			last += ((uint32_t)((unsigned char *)buf)[i]) << (8*(i-round_nbyte));
#ifdef NFB_IFC
		dpi_write32(comp->dev->path, comp->base + offset + round_nbyte, last);
#else
		dpiwrite(comp->dev->fd, comp->base + offset + round_nbyte, last);
#endif
	}
	return nbyte;
}
