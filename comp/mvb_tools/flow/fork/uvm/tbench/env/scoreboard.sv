// scoreboard.sv: Scoreboard for verification
// MVB_FORK UVM verification
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
//
// The scoreboard compares, per output port, the stream observed on the DUT
// output with the stream expected from the reference model. Each port is
// checked with an ordered comparer, which reports an error on the first
// duplicated or missing item (e.g. the MVB_FORK "register" re-presentation
// bug) and flags the test as failed via used().
//
// SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(ITEM_WIDTH, OUTPUT_PORTS) extends uvm_scoreboard;
    `uvm_component_utils(uvm_mvb_fork::scoreboard #(ITEM_WIDTH, OUTPUT_PORTS))

    // Analysis components.
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(ITEM_WIDTH)) analysis_imp_mvb_rx;

    uvm_analysis_export #(uvm_logic_vector::sequence_item #(ITEM_WIDTH)) analysis_imp_mvb_tx [OUTPUT_PORTS];

    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(ITEM_WIDTH)) port_cmp [OUTPUT_PORTS];

    model #(ITEM_WIDTH, OUTPUT_PORTS) m_model;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);

        analysis_imp_mvb_rx = new("analysis_imp_mvb_rx", this);

        for (int i = 0; i < OUTPUT_PORTS; i++) begin
            analysis_imp_mvb_tx[i] = new($sformatf("analysis_imp_mvb_tx_%0d", i), this);
        end
    endfunction

    function int unsigned success();
        int unsigned ret = 1;
        for (int i = 0; i < OUTPUT_PORTS; i++) begin
            ret &= port_cmp[i].success();
        end
        return ret;
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        for (int i = 0; i < OUTPUT_PORTS; i++) begin
            ret |= port_cmp[i].used();
        end
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);

        for (int i = 0; i < OUTPUT_PORTS; i++) begin
            port_cmp[i] = uvm_common::comparer_ordered
                #(uvm_logic_vector::sequence_item #(ITEM_WIDTH))::type_id::create($sformatf("port_cmp_%0d", i), this);
            port_cmp[i].model_tr_timeout_set(200us);
        end

        m_model = model #(ITEM_WIDTH, OUTPUT_PORTS)::type_id::create("m_model", this);

    endfunction

    function void connect_phase(uvm_phase phase);

        // Connects input data to the input of the model
        analysis_imp_mvb_rx.connect(m_model.model_mvb_in.analysis_export);

        // Model output and DUT output are compared on every port
        for (int i = 0; i < OUTPUT_PORTS; i++) begin
            m_model.model_mvb_out[i].connect(port_cmp[i].analysis_imp_model);
            analysis_imp_mvb_tx[i].connect(port_cmp[i].analysis_imp_dut);
        end

    endfunction

    function void report_phase(uvm_phase phase);
        string msg = "\n";
        int unsigned compared = 0;
        int unsigned errors   = 0;

        for (int i = 0; i < OUTPUT_PORTS; i++) begin
            compared += port_cmp[i].compared;
            errors   += port_cmp[i].errors;
        end

        msg = {msg, $sformatf("\tDATA Compared/errors: %0d/%0d\n", compared, errors)};

        if (this.success() && this.used() == 0) begin
            `uvm_info(
                get_type_name(), {
                msg,
                "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"
                }, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {
                      msg,
                      "\n\n\t---------------------------------------\n\t----     VERIFICATION FAILED       ----\n\t---------------------------------------"
                      }, UVM_NONE)
        end

    endfunction

endclass
