// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2023-2024 CESNET z. s. p. o.
// Author: Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
//         Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(ITEM_WIDTH, TX_PORTS) extends uvm_scoreboard;
    `uvm_component_utils(uvm_mvb_demux::scoreboard #(ITEM_WIDTH, TX_PORTS))

    // Analysis components.
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(ITEM_WIDTH + $clog2(TX_PORTS)))  rx_mvb_analysis_imp;
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(ITEM_WIDTH))                     tx_mvb_analysis_exp [TX_PORTS -1 : 0];

    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(ITEM_WIDTH)) port_cmp[TX_PORTS -1 : 0];

    model#(ITEM_WIDTH, TX_PORTS) m_model;

    function new(string name, uvm_component parent);
        super.new(name, parent);

        for (int port = 0; port < TX_PORTS; port ++) begin
            tx_mvb_analysis_exp[port] = new($sformatf("tx_mvb_analysis_exp_%0d", port), this);
        end

        rx_mvb_analysis_imp = new("rx_mvb_analysis_imp", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;

        for (int i = 0; i < TX_PORTS; i++) begin
            ret |= this.port_cmp[i].used();
            ret |= this.port_cmp[i].errors != 0;
        end

        return ret;
    endfunction

    function void build_phase(uvm_phase phase);

        for (int port = 0; port < TX_PORTS; port ++) begin
            port_cmp[port] = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(ITEM_WIDTH))::type_id::create($sformatf("port_cmp_%0d", port), this);
            port_cmp[port].model_tr_timeout_set(10us);
        end

        m_model = model #(ITEM_WIDTH, TX_PORTS)::type_id::create("m_model", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        rx_mvb_analysis_imp.connect(m_model.rx_mvb_analysis_fifo.analysis_export);

        for (int port = 0; port < TX_PORTS; port++) begin
            tx_mvb_analysis_exp[port]        .connect(port_cmp[port].analysis_imp_dut);
            m_model.tx_mvb_analysis_imp[port].connect(port_cmp[port].analysis_imp_model);
        end
    endfunction

    function void report_phase(uvm_phase phase);
        string msg = "\n";
        int unsigned compared = 0;
        int unsigned errors   = 0;

        for (int port = 0; port < TX_PORTS; port++) begin
            compared = compared + port_cmp[port].compared;
            errors   = errors   + port_cmp[port].errors;
        end

        msg = {msg, $sformatf("\tDATA Compared/errors: %0d/%0d\n",  compared, errors)};

        if (this.used() == 0) begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------", msg), UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------", msg), UVM_NONE)
        end
    endfunction
endclass
