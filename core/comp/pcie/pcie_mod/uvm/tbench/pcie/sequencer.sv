// sequencer.sv: Sequencer for pcie
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class pcie_info;

    typedef struct {
        uvm_pcie::request_header hdr;
        int unsigned lower_address;
        int unsigned byte_count;
        int unsigned rest_length; // in DWORDS
    } rq_info;

    logic [8-1:0] cq_tags[logic [16-1:0]][logic [8-1:0]];
    rq_info       rq_hdr[$];

    function new();
        cq_tags.delete();
        rq_hdr.delete();
    endfunction


    function void requester_add(logic [16-1:0] requester_id);
        //Remove all tags from this requester ID
        if (!cq_tags.exists(requester_id)) begin
            cq_tags[requester_id].delete();
        end
    endfunction

    function void requester_remove(logic [16-1:0] requester_id);
        cq_tags.delete(requester_id);
    endfunction

    function void cq_tag_add(logic [16-1:0] requester_id, logic [8-1:0] tag);
        cq_tags[requester_id][tag] = tag;
    endfunction

    function void cq_tag_remove(logic [16-1:0] requester_id, logic [8-1:0] tag);
        if (cq_tags.exists(requester_id)) begin
            cq_tags[requester_id].delete(tag);
        end
    endfunction
endclass

class sequencer extends uvm_sequencer #(uvm_pcie::header);
    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_component_param_utils(uvm_pcie::sequencer)

    uvm_reset::sync_terminate reset_sync;

    //responses
    uvm_tlm_analysis_fifo #(uvm_pcie::completer_header) fifo_cc;
    uvm_tlm_analysis_fifo #(uvm_pcie::request_header)   fifo_rq;

    pcie_info info;

    // Constructor
    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
        reset_sync = new();
        fifo_cc = new("fifo_cc", this);
        fifo_rq = new("fifo_rq", this);
        info    = new();
    endfunction: new

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        uvm_config_db #(pcie_info)::set(this, "", "pcie_info", info);
    endfunction

    task run_cc();
        forever begin
            uvm_pcie::completer_header pcie_cc;
            int unsigned  move;
            int unsigned length;
            fifo_cc.get(pcie_cc);

            length = pcie_cc.length != 0 ? pcie_cc.length : 1024;
            move   = pcie_cc.lower_address & 2'b11;

            //if completed the nremove tag
            if ((pcie_cc.byte_count <= (length*4 - move))) begin
                info.cq_tag_remove(pcie_cc.requester_id, pcie_cc.tag);
            end
        end
    endtask

    task run_rq();
        pcie_info::rq_info rq_tr;
        forever begin
            uvm_pcie::request_header pcie_rq;
            fifo_rq.get(pcie_rq);

            if ({pcie_rq.fmt[3-1:1], pcie_rq.pcie_type} == {2'b00, 5'b00000}) begin
                logic [4-1:0] lbe = (pcie_rq.length != 1) ? pcie_rq.lbe : pcie_rq.fbe;

                rq_tr.hdr         = pcie_rq;
                rq_tr.lower_address = {pcie_rq.address[7-1 : 2], 2'b00} + uvm_pcie::encode_fbe(pcie_rq.fbe);
                rq_tr.byte_count  = unsigned'(pcie_rq.length * 4) - unsigned'(uvm_pcie::encode_fbe(pcie_rq.fbe)) - (4-unsigned'(encode_lbe(lbe)));
                rq_tr.rest_length = pcie_rq.length;
                info.rq_hdr.push_back(rq_tr);
            end
        end
    endtask


    task run_phase(uvm_phase phase);
        fork
            run_cc();
            run_rq();
        join
    endtask
endclass

