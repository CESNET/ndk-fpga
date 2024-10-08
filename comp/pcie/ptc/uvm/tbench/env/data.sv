//-- data.sv: Model of implementation
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša  <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class pcie_data#(MEATA_WIDTH) extends uvm_object;
    `uvm_object_param_utils(uvm_ptc::pcie_data#(MEATA_WIDTH))

    logic [MEATA_WIDTH-1:0]       meta;
    logic [32-1:0]                data[];

    function new(string name = "");
        super.new(name);
    endfunction
endclass


class dma_header_rq extends uvm_object;
    `uvm_object_utils(uvm_ptc::dma_header_rq)

    uvm_ptc_info::sequence_item hdr;
    logic [32-1:0] data[];

    function new(string name = "");
        super.new(name);
    endfunction
endclass


class dma_header_rc extends uvm_object;
    `uvm_object_utils(uvm_ptc::dma_header_rc)

    int unsigned port;
    int unsigned length;
    int unsigned completed;
    int unsigned tag;
    int unsigned unit_id;

    logic [32-1:0] data[];

    function new(string name = "");
        super.new(name);
    endfunction
endclass

