/*
 * file       : dpi_pcap.c
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: pcap open
 * date       : 2022
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


#ifndef DPI_PCAP_H
#define DPI_PCAP_H

#include "svdpi.h"


//////////////////////////////////////////
// READ INTERFACE
void* dpi_pcap_read_open(const char* file);
void  dpi_pcap_read_close(void* ptr);
int   dpi_pcap_read_data_get(void* file_ptr,const void** data_ptr, unsigned int* size);
void  dpi_pcap_read_data_extract(void* in, const svOpenArrayHandle out);

//////////////////////////////////////////
// WRITE INTERFACE
void* dpi_pcap_write_open(int linktype, const char* file);
void dpi_pcap_write_close(void* ptr);
void dpi_pcap_write_data(void* file_ptr, const svOpenArrayHandle data);



#endif
