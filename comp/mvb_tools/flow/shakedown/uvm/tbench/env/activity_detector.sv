// activity_detector.sv: Generates a sequence of port numbers from which items are read
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class activity_detector #(int unsigned TX_ITEMS, int unsigned ITEM_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_mvb_shakedown::activity_detector #(TX_ITEMS, ITEM_WIDTH))

    // Inputs
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(ITEM_WIDTH)) analysis_export[TX_ITEMS];

    // Outputs
    uvm_analysis_port #(int unsigned) analysis_port;

    // Watchdogs for the ports
    port_watchdog #(ITEM_WIDTH) m_port_watchdog[TX_ITEMS];

    function new(string name = "activity_detector", uvm_component parent = null);
        super.new(name, parent);

        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            analysis_export[i] = new($sformatf("analysis_export_%0d", i), this);
        end
        analysis_port = new("analysis_port", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            m_port_watchdog[i] = port_watchdog #(ITEM_WIDTH)::type_id::create($sformatf("port_watchdog_%0d", i), this);
            m_port_watchdog[i].port_number = i;
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            analysis_export[i].connect(m_port_watchdog[i].analysis_export);
            m_port_watchdog[i].analysis_port.connect(analysis_port);
        end
    endfunction

endclass
