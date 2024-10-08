/*
 * file       : reader.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: reading pcap files
 * date       : 2022
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

import "DPI-C" context function chandle dpi_pcap_read_open(string file);
import "DPI-C" context function void    dpi_pcap_read_close(chandle ptr);
import "DPI-C" context function int     dpi_pcap_read_data_get(chandle file_ptr, output chandle data_ptr, output int unsigned size);
import "DPI-C" context function void    dpi_pcap_read_data_extract(chandle in, inout byte unsigned out[]);


class reader;
    chandle file;

    function new();
        file = null;
    endfunction

    function int open(string file_name);
        file = dpi_pcap_read_open(file_name);
        return (file != null);
    endfunction

    function void close();
        dpi_pcap_read_close(file);
        file = null;
    endfunction

    function err_code read(output byte unsigned data[]);
        chandle pcap_data;
        int unsigned  pcap_size;

        if (dpi_pcap_read_data_get(file, pcap_data, pcap_size) != 1) begin
            return RET_ERR;
        end

        data = new[pcap_size];
        dpi_pcap_read_data_extract(pcap_data, data);
        return RET_OK;
    endfunction
endclass
