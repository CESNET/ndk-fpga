/*
 * file       : reader.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: reading pcap files
 * date       : 2022
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

import "DPI-C" context function chandle dpi_pcap_write_open(int linktype, string file);
import "DPI-C" context function void    dpi_pcap_write_close(chandle ptr);
import "DPI-C" context function int     dpi_pcap_write_data(chandle file_ptr, byte unsigned data[]);


class writer;
    chandle file;

    function new();
        file = null;
    endfunction

    function int open(string file_name, int linktype = 1);
        file = dpi_pcap_write_open(linktype, file_name);
        return (file != null);
    endfunction

    function void close();
        dpi_pcap_write_close(file);
        file = null;
    endfunction

    function void write(byte unsigned data[]);
        dpi_pcap_write_data(file, data);
    endfunction
endclass
