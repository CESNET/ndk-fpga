// status_model.sv: Model of implementation of status logic
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class status_model #(ITEMS, WRITE_PORTS, READ_PORTS, ALMOST_FULL_OFFSET, ALMOST_EMPTY_OFFSET) extends uvm_component;
    `uvm_component_param_utils(uvm_fifox_multi::status_model #(ITEMS, WRITE_PORTS, READ_PORTS, ALMOST_FULL_OFFSET, ALMOST_EMPTY_OFFSET))

    // Model inputs
    uvm_probe::cbs_simple #(1+$clog2(WRITE_PORTS+1)+$clog2(READ_PORTS+1)) status_in;

    // Model outputs
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(2)) model_out;

    function new(string name = "status_model", uvm_component parent = null);
        super.new(name, parent);

        model_out = new("model_out", this);

    endfunction

    function void build_phase(uvm_phase phase);

        status_in = uvm_probe::cbs_simple #(1+$clog2(WRITE_PORTS+1)+$clog2(READ_PORTS+1))::type_id::create("status_in", this);

        uvm_probe::pool::get_global_pool().get({ "probe_event_component_", "testbench.DUT_U.VHDL_DUT_U.full_gen.fifox_multi_full_i", ".probe_status" }).add_callback(status_in);

    endfunction

    task run_phase(uvm_phase phase);

        uvm_logic_vector::sequence_item #(2) tr_out;

        logic afull;
        logic aempty;

        logic [$clog2(WRITE_PORTS+1)-1 : 0] wr;
        logic [$clog2(READ_PORTS+1) -1 : 0] rd;
        logic wr_en;

        int unsigned status_wr = 0;
        int unsigned status_rd[$];
        for (int i = 0; i < 2; i++) status_rd.push_back(0);

        send_initial_transactions();

        forever begin

            status_in.get({ wr_en, wr, rd });

            afull  = (status_wr + wr >= ITEMS - ALMOST_FULL_OFFSET) ? 1 : 0;
            aempty = (status_rd[$] - rd <= ALMOST_EMPTY_OFFSET)     ? 1 : 0;

            tr_out = uvm_logic_vector::sequence_item #(2)::type_id::create("tr_out", this);
            tr_out.data = { afull, aempty };
            tr_out.start[this.get_full_name()] = $time();
            model_out.write(tr_out);

            // Updates the read status
            status_rd.pop_back();
            status_rd.push_front(status_wr);
            foreach (status_rd[i]) status_rd[i] -= rd;

            // Updates the write status
            if (wr_en) status_wr += wr;
            status_wr -= rd;

        end

    endtask

    task send_initial_transactions();

        uvm_logic_vector::sequence_item #(2) tr_out;
        tr_out = uvm_logic_vector::sequence_item #(2)::type_id::create("tr_out", this);
        tr_out.data = { 1'b0, 1'b1 };
        tr_out.start[this.get_full_name()] = $time();
        model_out.write(tr_out);

    endtask

endclass
