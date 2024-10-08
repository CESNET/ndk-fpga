/*
 * dpi_pcap.c: Wrapper of libPCAP for SystemVerilog
 * Copyright (C) 2016 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

#include <pcap.h>
#include "svdpi.h"
#include "dpi_pcap.h"

extern void dpi_pcap_buffer_alloc(int size);



void* dpi_pcap_open_offline(const char* file) {
    pcap_t *pcap;
    char errbuf[PCAP_ERRBUF_SIZE];
    pcap = pcap_open_offline(file, errbuf);
    if(pcap == NULL) {
        printf("DPI PCAP: Error opening PCAP file - %s\n", errbuf);
        fflush(stdout);
    }
    return pcap;
}


void* dpi_pcap_open_dead(int linktype, int snaplen) {
    pcap_t *pcap;
    pcap = pcap_open_dead(linktype, snaplen);
    if(pcap == NULL) {
        printf("DPI PCAP: Error opening dead PCAP interface\n");
        fflush(stdout);
    }
    return pcap;
}


void* dpi_pcap_dump_open(void* p, const char* fname) {
    pcap_dumper_t *dump;
    dump = pcap_dump_open(p, fname);
    if(dump == NULL) {
        printf("DPI PCAP: Error creating PCAP file\n");
        fflush(stdout);
    }
    return dump;
}


void dpi_pcap_dump_close(void *p) {
    pcap_dump_close(p);
}


void dpi_pcap_close(void *pcap) {
    pcap_close(pcap);
}


void dpi_pcap_dump(void* user, const dpi_pcap_pkthdr_t* h, const svOpenArrayHandle sp) {
    struct pcap_pkthdr hdr;
    hdr.len = h->len;
    hdr.caplen = h->caplen;
    hdr.ts.tv_sec = h->ts_sec;
    hdr.ts.tv_usec = h->ts_usec;
    pcap_dump(user, &hdr, (unsigned char *)svGetArrayPtr(sp));
}


int dpi_pcap_next_internal(void* pcap, dpi_pcap_pkthdr_t* pkt_header, const svOpenArrayHandle buffer) {
    struct pcap_pkthdr *h;
    const unsigned char *p;
    unsigned char *b;
    int ret;
    ret = pcap_next_ex(pcap, &h, &p);
    if(ret == 1) {
        b = (unsigned char *)svGetArrayPtr(buffer);
        memcpy(b, p, h->caplen);
        pkt_header->len = h->len;
        pkt_header->caplen = h->caplen;
        pkt_header->ts_sec = h->ts.tv_sec;
        pkt_header->ts_usec = h->ts.tv_usec;
    }
    return ret;
}
