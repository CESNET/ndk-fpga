/*
 * file       : pkg.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: this package simplifie pcap reading
 * date       : 2022
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef UVM_PCAP_PKG
`define UVM_PCAP_PKG


package uvm_pcap;

    typedef enum {RET_OK, RET_ERR} err_code;

    `include "reader.sv"
    `include "writer.sv"
endpackage

`endif
