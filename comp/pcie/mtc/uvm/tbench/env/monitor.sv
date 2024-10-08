//-- monitor.sv: Monitor for MVB environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class monitor #(MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_logic_vector::monitor#(MI_DATA_WIDTH);
    `uvm_component_param_utils(uvm_mtc::monitor #(MI_DATA_WIDTH, MI_ADDR_WIDTH))

    // Analysis port
    typedef monitor #(MI_DATA_WIDTH, MI_ADDR_WIDTH) this_type;
    uvm_analysis_imp #(uvm_logic_vector::sequence_item #(MI_DATA_WIDTH), this_type) analysis_export;

    uvm_reset::sync_terminate reset_sync;
    local uvm_logic_vector::sequence_item #(MI_DATA_WIDTH) hi_tr;
    int read_cnt;

    function new (string name, uvm_component parent);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
        hi_tr = null;
        reset_sync = new();
        read_cnt = 0;
    endfunction

    virtual function void write(uvm_logic_vector::sequence_item #(MI_DATA_WIDTH) tr);
        if (reset_sync.has_been_reset()) begin
            hi_tr = null;
        end

        hi_tr = uvm_logic_vector::sequence_item #(MI_DATA_WIDTH)::type_id::create("hi_tr");
        hi_tr.copy(tr);
        read_cnt++;
        analysis_port.write(hi_tr);

    endfunction
endclass
