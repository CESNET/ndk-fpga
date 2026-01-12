//-- tr_planner.sv: Transaction planner
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class tr_planner  extends uvm_component;
    `uvm_component_param_utils(uvm_crdt::tr_planner)

    uvm_analysis_imp#(uvm_pcie::header, tr_planner) analysis_export;

    int unsigned cnt_ph   ;
    int unsigned cnt_nph  ;
    int unsigned cnt_cplh ;
    int unsigned cnt_pd   ;
    int unsigned cnt_npd  ;
    int unsigned cnt_cpld ;


    function new(string name, uvm_component parent);
        super.new(name, parent);
        analysis_export = new("analysis_imp", this);
        cnt_ph   = 0;
        cnt_nph  = 0;
        cnt_cplh = 0;
        cnt_pd   = 0;
        cnt_npd  = 0;
        cnt_cpld = 0;
    endfunction

    virtual function void write(uvm_pcie::header req);
        int unsigned hdr_len = req.length != 0 ? req.length : 1024;

        case ({req.fmt, req.pcie_type})
            8'b00000000 :
            begin
                cnt_nph++;
            end
            8'b00100000 :
            begin
                cnt_nph++;
            end
            8'b01001010 :
            begin
                cnt_cplh++;
                cnt_cpld += (hdr_len + 3)/4;
            end
            8'b01000000 :
            begin
                cnt_ph++;
                cnt_pd += (hdr_len + 3)/4;
            end
            8'b01100000 :
            begin
                cnt_ph++;
                cnt_pd += (hdr_len + 3)/4;
            end
        endcase
    endfunction
endclass

