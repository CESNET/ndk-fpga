/*
 * dpi_pcap.sv: Wrapper of libPCAP for SystemVerilog
 * Copyright (C) 2016 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

package dpi_pcap;

    byte unsigned dpi_pcap_buffer[65535]; // do not touch this from your SV code!



// START OF PUBLIC INTERFACE ///////////////////////////////////////////////////

    typedef chandle dpi_pcap_t;

    typedef chandle dpi_pcap_dumper_t;

    typedef byte unsigned dpi_pcap_array_t[]; // just a hack to work-around syntax to enable function returning array

    typedef struct {
        int unsigned caplen;
        int unsigned len;
        int unsigned ts_sec;
        int unsigned ts_usec;
    } dpi_pcap_pkthdr_t;

    function int dpi_pcap_next_ex(dpi_pcap_t p, output dpi_pcap_pkthdr_t pkt_header, output byte unsigned pkt_data[]);
        int ret;
        ret = dpi_pcap_next_internal(p, pkt_header, dpi_pcap_buffer);
        if(ret == 1)
            pkt_data = new[pkt_header.caplen](dpi_pcap_buffer);
        return ret;
    endfunction

    function dpi_pcap_array_t dpi_pcap_next(dpi_pcap_t p, output dpi_pcap_pkthdr_t h);
        byte unsigned ret[];
        ret = null;
        if(dpi_pcap_next_internal(p, h, dpi_pcap_buffer) == 1)
            ret = new[h.caplen](dpi_pcap_buffer);
        return ret;
    endfunction

    import "DPI-C" context function dpi_pcap_t dpi_pcap_open_offline(string file);

    import "DPI-C" context function dpi_pcap_t dpi_pcap_open_dead(int linktype, int snaplen);

    import "DPI-C" context function dpi_pcap_dumper_t dpi_pcap_dump_open(dpi_pcap_t p, string fname);

    import "DPI-C" context function void dpi_pcap_dump_close(dpi_pcap_dumper_t p);

    import "DPI-C" context function void dpi_pcap_close(dpi_pcap_t pcap);

    import "DPI-C" context function void dpi_pcap_dump(dpi_pcap_dumper_t user, dpi_pcap_pkthdr_t h, byte unsigned sp[]);

// END OF PUBLIC INTERFACE /////////////////////////////////////////////////////



    import "DPI-C" context function int dpi_pcap_next_internal(dpi_pcap_t pcap, output dpi_pcap_pkthdr_t pkt_header, inout byte unsigned buffer[]);

endpackage
