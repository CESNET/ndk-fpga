/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

////////////////////////////////////////////////
// callback for
class pcie_tag_cbs extends sv_common_pkg::MonitorCbs;
     tag_manager              tags;

     function new (tag_manager tags);
        this.tags = tags;
     endfunction

    virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
        PcieRequest tr;

        //register tag
        $cast(tr, transaction);
        if(tr.type_tr == PCIE_RQ_READ) begin
            tags.set(tr.tag);
        end
    endtask
endclass

//////////////////////////////////////////////////
// base agent for pcie
class agent #(RCB, MPS);
    string inst;
    tag_manager          tags;
    pcie_tag_cbs         tags_req_cbs;

    //root complex
    //ram  #(ADDR_WIDTH, MPS, MRRS) root;
    //pcie_driver_cbs               root_cbs;

    //pcie controler => divede transaction on smaller transaction
    PcieCompletionSequencer #(RCB, MPS) pcie_sq;
    pcie_driver_cbs                     pcie_sq_cbs;

    function new (string inst, sv_common_pkg::tTransMbx mbx_input);
        tags         = new({inst, " TAG MANAGER"});
        tags_req_cbs = new(tags);

        //ram module
        //root_cbs      = new();
        //root          = new("ROOT COMPLEX RAM", pcie_request_cbs.mbx_response, ram_modul, tags);
        //root.setCallbacks(root_cbs);

        //ram to pcie
        pcie_sq_cbs = new(4); //because tag shuld be unregistred as late as possible
        pcie_sq = new({inst, " PCIE SEQUENCER"}, mbx_input, tags);
        pcie_sq.setCallbacks(pcie_sq_cbs);
    endfunction

    virtual task setEnabled();
        //root.setEnabled();
        pcie_sq.setEnabled();
    endtask

    virtual task setDisabled();
        //root.setDisabled();
        pcie_sq.setDisabled();
    endtask

    virtual function void verbosity_set(int unsigned level);
        //root.verbosity_set(level);
        pcie_sq.verbosity_set(level);
    endfunction

    virtual function void rq_setCallbacks(sv_common_pkg::MonitorCbs cbs);
    endfunction

    virtual function void rq_ifg_set(ifg_config_setup cfg);
    endfunction

    virtual function void rc_ifg_set(ifg_config_setup cfg);
    endfunction
endclass
