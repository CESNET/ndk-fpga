//-- sync_tag.sv: Synchronization of tags
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sync_tag extends uvm_component;
    `uvm_component_utils(uvm_ptc_info::sync_tag)

    logic [8-1 : 0] list_of_tags [logic [8-1 : 0]];
    int tag_cnt = 0;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    task add_element(logic[8-1 : 0] tag);
        string msg;
        list_of_tags[tag] = tag;
        tag_cnt++;
    endtask

    task remove_element(logic[8-1 : 0] tag);
        string msg;
        list_of_tags.delete(tag);
        tag_cnt--;
    endtask

endclass
