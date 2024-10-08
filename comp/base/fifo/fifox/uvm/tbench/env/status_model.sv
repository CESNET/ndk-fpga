// status_model.sv: Model of implementation of status logic
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class status_model #(STATUS_WIDTH, ITEMS, ALMOST_FULL_OFFSET, ALMOST_EMPTY_OFFSET) extends uvm_component;
    `uvm_component_param_utils(uvm_fifox::status_model #(STATUS_WIDTH, ITEMS, ALMOST_FULL_OFFSET, ALMOST_EMPTY_OFFSET))

    // Model inputs
    uvm_probe::cbs_simple #(2) wr_and_rd_en_in;

    // Model outputs
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(STATUS_WIDTH+2)) model_out;

    function new(string name = "status_model", uvm_component parent = null);
        super.new(name, parent);

        model_out = new("model_out", this);

    endfunction

    function void build_phase(uvm_phase phase);

        wr_and_rd_en_in = uvm_probe::cbs_simple #(2)::type_id::create("wr_and_rd_en_in", this);

        uvm_probe::pool::get_global_pool().get({ "probe_event_component_", "testbench.DUT_U.VHDL_DUT_U", ".probe_status" }).add_callback(wr_and_rd_en_in);

    endfunction

    task run_phase(uvm_phase phase);

        uvm_logic_vector::sequence_item #(STATUS_WIDTH+2) tr_out;

        int unsigned status = 0;

        logic [STATUS_WIDTH-1 : 0] logic_status;
        logic afull;
        logic aempty;

        logic wr_en;
        logic rd_en;

        forever begin

            wr_and_rd_en_in.get({ wr_en, rd_en });
            if (wr_en) status++;
            if (rd_en) status--;

            logic_status = status;
            afull  = (status >= ITEMS - ALMOST_FULL_OFFSET) ? 1 : 0;
            aempty = (status <= ALMOST_EMPTY_OFFSET)        ? 1 : 0;

            tr_out = uvm_logic_vector::sequence_item #(STATUS_WIDTH+2)::type_id::create("tr_out", this);
            tr_out.data = { logic_status, afull, aempty };
            tr_out.start[this.get_full_name()] = $time();
            model_out.write(tr_out);
        end

    endtask

endclass
