/*
 * file       : dpi_pcap.c
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: pcap open
 * date       : 2022
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


#include "dpi_pcap.h"

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <pcap.h>



//////////////////////////////////////////
// READ INTERFACE
void * dpi_pcap_read_open( const char* file){
    pcap_t *pcap;
    char errbuf[PCAP_ERRBUF_SIZE];
    pcap = pcap_open_offline(file, errbuf);
    if(pcap == NULL) {
        printf("DPI PCAP: Error opening PCAP file - %s for reading\n", errbuf);
        fflush(stdout);
    }
    return pcap;
}


void dpi_pcap_read_close(void* ptr){
    pcap_close(ptr);
}


int dpi_pcap_read_data_get(void *file_ptr, const void** data_ptr, unsigned int* size){
    struct pcap_pkthdr *hdr;
    int ret;

    ret = pcap_next_ex(file_ptr, &hdr, (const u_char **)data_ptr);
    *size = hdr->caplen;

    return ret;
}

void dpi_pcap_read_data_extract(void* in, const svOpenArrayHandle out){
    void * ptr;
    int unsigned ptr_size;

    ptr      = svGetArrayPtr(out);
    ptr_size = svSizeOfArray(out);

    memcpy(ptr, in, ptr_size);
}


//////////////////////////////////////////
// WRITE INTERFACE
struct dpci_pcap_write_st{
    pcap_t        *pcap;
    pcap_dumper_t *pcap_dumper;
};


void* dpi_pcap_write_open(int linktype, const char* file){
    struct dpci_pcap_write_st * pcap;

    pcap = malloc(sizeof (struct dpci_pcap_write_st));

    if (pcap == NULL){
        return NULL;
    }

    pcap->pcap = pcap_open_dead(linktype, 65535);
    if(pcap->pcap == NULL) {
        free(pcap);
        printf("DPI PCAP: Error opening dead PCAP interface\n");
        fflush(stdout);
        return NULL;
    }

    pcap->pcap_dumper = pcap_dump_open(pcap->pcap, file);
    if(pcap->pcap_dumper == NULL) {
        pcap_close(pcap->pcap);
        free(pcap);
        printf("DPI PCAP: Error opening PCAP file - %s for writing\n", file);
        fflush(stdout);
        return NULL;
    }
    return pcap;
}

void dpi_pcap_write_close(void* ptr){
    struct dpci_pcap_write_st * pcap = ptr;

    pcap_close(pcap->pcap);
    pcap_dump_close(pcap->pcap_dumper);
    free(pcap);
}

void dpi_pcap_write_data(void* file_ptr, const svOpenArrayHandle data){
    struct dpci_pcap_write_st * pcap = file_ptr;
    struct pcap_pkthdr hdr;
    int unsigned len;

    len = svSizeOfArray(data);
    hdr.len        = len;
    hdr.caplen     = len;
    hdr.ts.tv_sec  = 0;
    hdr.ts.tv_usec = 0;
    pcap_dump((unsigned char *) pcap->pcap_dumper, &hdr, (unsigned char *)svGetArrayPtr(data));
}

