/*!
 * \file test.sv
 * \brief Test Cases
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import dpi_pcap::*;



module testbench();

    initial begin
        dpi_pcap_t pcap;
        dpi_pcap_pkthdr_t h;
        byte unsigned p[];
        pcap = dpi_pcap_open_offline("test.pcap");
        if(!pcap)
            $stop();
        while(dpi_pcap_next_ex(pcap, h, p) == 1)
            $write("Packet with length of %4d bytes, starting with: %02x%02x%02x%02x%02x%02x%02x%02x\n", p.size, p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7]);
        dpi_pcap_close(pcap);
    end

endmodule

