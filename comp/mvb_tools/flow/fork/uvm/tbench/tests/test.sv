// test.sv: Verification test
// MVB_FORK UVM verification
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause


class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);

    uvm_mvb_fork::env #(ITEMS, ITEM_WIDTH, OUTPUT_PORTS, USE_DST_RDY) m_env;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_mvb_fork::env #(ITEMS, ITEM_WIDTH, OUTPUT_PORTS, USE_DST_RDY)::type_id::create("m_env", this);
    endfunction

    task run_seq_rx(uvm_phase phase);
        virt_sequence#(ITEM_WIDTH, OUTPUT_PORTS) m_vseq;
        time time_end;

        phase.raise_objection(this, "Start of rx sequence");

        m_vseq = virt_sequence#(ITEM_WIDTH, OUTPUT_PORTS)::type_id::create("m_vseq");
        assert(m_vseq.randomize());
        m_vseq.start(m_env.vscr);

        time_end = $time + 1ms;
        while ($time < time_end && m_env.m_scoreboard.used() != 0) begin
            #(500ns);
        end

        phase.drop_objection(this, "End of rx sequence");
    endtask


    virtual task run_phase(uvm_phase phase);
        run_seq_rx(phase);
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass


// Directed test for the MVB_FORK VERSION = "register" data duplication bug.
//
// If RX_SRC_RDY falls while RX_DST_RDY is not set, the fork may clear the
// per-port send_reg even though no RX transfer happened; when the source
// re-presents the held item, the port that already consumed it consumes it
// again -> duplicated item on that port. The random test (ex_test) can not
// trigger this.
//
// Stimulus: one item per beat (T0..T7), port 1 is back-pressured in T2.
// Expected: register build -> scoreboard reports the duplicated D2,
//           logic/simple build -> clean pass (control).

class directed_test_base extends uvm_test;

    localparam int WORD_BITS = ITEMS * ITEM_WIDTH;

    localparam logic [ITEMS-1:0] VLD_ITEM0 = 1'b1; // only item 0 valid (zero-extended)

    uvm_mvb_fork::env #(ITEMS, ITEM_WIDTH, OUTPUT_PORTS, USE_DST_RDY) m_env;
    string mode_name;

    // Observe the reset monitor
    uvm_tlm_analysis_fifo #(uvm_reset::sequence_item) reset_fifo;

    virtual mvb_if #(.ITEMS(ITEMS), .ITEM_WIDTH(ITEM_WIDTH)) vif_rx;

    virtual mvb_if #(.ITEMS(ITEMS), .ITEM_WIDTH(ITEM_WIDTH)) vif_tx[OUTPUT_PORTS];

    `uvm_component_utils(test::directed_test_base)

    function new(string name, uvm_component parent);
        super.new(name, parent);
        mode_name = "?";
    endfunction

    function void build_phase(uvm_phase phase);
        // The test drives the clocking blocks itself.
        // MVb agents must be passive.
        uvm_config_db#(bit)::set(this, "m_env", "agents_active", 0);

        if ((mode_name == "register" && VERSION != "register") ||
            (mode_name == "logic" && VERSION == "register")) begin
            `uvm_error(
                get_type_name(),
                $sformatf(
                "test expects VERSION=\"%s\" but the DUT was built with VERSION=\"%s\" - build the matching variant.",
                mode_name,
                VERSION));
        end

        m_env      = uvm_mvb_fork::env #(ITEMS, ITEM_WIDTH, OUTPUT_PORTS, USE_DST_RDY)::type_id::create("m_env", this);
        reset_fifo = new("reset_fifo", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        uvm_config_db#(virtual mvb_if#(.ITEMS(ITEMS), .ITEM_WIDTH(ITEM_WIDTH)))::get(null, "", "vif_rx", vif_rx);
        for (int i = 0; i < OUTPUT_PORTS; i++) begin
            uvm_config_db#(
                virtual mvb_if#(.ITEMS(ITEMS), .ITEM_WIDTH(ITEM_WIDTH))
            )::get(
                null, "", $sformatf("vif_tx_%0d", i), vif_tx[i]
            );
        end
        m_env.m_reset.analysis_port.connect(reset_fifo.analysis_export);
    endfunction

    virtual task wait_reset_done();
        uvm_reset::sequence_item tr;
        bit                      reset_asserted;
        int unsigned             tries;

        reset_asserted = 0;
        tries          = 0;
        while (1) begin
            reset_fifo.get(tr);
            if (tr.reset === 1'b1) begin
                reset_asserted = 1;
            end else if (reset_asserted) begin
                break;
            end
            if (tries > 10000) begin
                `uvm_fatal("directed_test_base", "Timed out waiting for reset deassert");
            end
            tries++;
        end
    endtask

    virtual function void row(logic [WORD_BITS-1:0] data, logic [ITEMS-1:0] vld,
                              logic src, logic [OUTPUT_PORTS-1:0] tx_dst_rdy);
        vif_rx.driver_rx_cb.DATA    <= data;
        vif_rx.driver_rx_cb.VLD     <= vld;
        vif_rx.driver_rx_cb.SRC_RDY <= src;
        for (int i = 0; i < OUTPUT_PORTS; i++) begin
            vif_tx[i].driver_tx_cb.DST_RDY <= tx_dst_rdy[i];
        end
    endfunction

    virtual task tick();
        @(vif_rx.driver_rx_cb);
    endtask

    virtual task directed_stimulus();
        logic [WORD_BITS-1:0]    d1, d2, d3;
        logic [OUTPUT_PORTS-1:0] all_rdy;
        logic [OUTPUT_PORTS-1:0] hold_p1;

        if (OUTPUT_PORTS < 2) begin
            `uvm_fatal("directed_test_base", "Directed test requires OUTPUT_PORTS >= 2");
        end

        all_rdy = {OUTPUT_PORTS{1'b1}};
        hold_p1 = all_rdy;
        hold_p1[1] = 1'b0;

        d1 = {WORD_BITS/8 {8'hA1}};
        d2 = {WORD_BITS/8 {8'hB2}};
        d3 = {WORD_BITS/8 {8'hC3}};

        // T0: idle after reset (let the DUT leave any reset-time X state).
        row('x, 'x, 1'b0, all_rdy);
        repeat (3) tick();

        // T1: all ports ready -> D1 is taken by RX and every port.
        row(d1, VLD_ITEM0, 1'b1, all_rdy);
        tick();

        // T2: port 1 held -> only the ready port(s) take D2.
        row(d2, VLD_ITEM0, 1'b1, hold_p1);
        tick();

        // T3: the source retracts while RX_DST_RDY is not set (the trigger).
        row('x, 'x, 1'b0, hold_p1);
        tick();

        // T4: the held port becomes ready while the source is retracted.
        row('x, 'x, 1'b0, all_rdy);
        tick();

        // T5: re-present D2.
        row(d2, VLD_ITEM0, 1'b1, all_rdy);
        tick();

        // T6: final item, all ports ready.
        row(d3, VLD_ITEM0, 1'b1, all_rdy);
        tick();

        // T7: idle.
        row('x, 'x, 1'b0, all_rdy);
        repeat (4) tick();
    endtask

    virtual task run_phase(uvm_phase phase);
        uvm_reset::sequence_reset m_reset;
        uvm_reset::sequence_run   m_run;

        phase.raise_objection(this, "Start of directed test");

        // Drive defined idle values on the clocking block outputs; the
        // passive agents drive nothing and the properties require defined
        // signals once reset is deasserted.
        row('0, '0, 1'b0, {OUTPUT_PORTS{1'b1}});

        // Reset the DUT; the background "run" sequence keeps reset deasserted.
        m_reset = uvm_reset::sequence_reset::type_id::create("m_reset");
        m_run   = uvm_reset::sequence_run::type_id::create("m_run");
        fork
            begin
                m_reset.randomize();
                m_reset.start(m_env.vscr.m_reset);
                m_run.randomize();
                m_run.start(m_env.vscr.m_reset);
            end
        join_none
        wait_reset_done();

        uvm_root::get().set_report_id_action_hier("testbench.property_wr", UVM_NO_ACTION);

        directed_stimulus();

        #(210us);

        `uvm_info("directed_test_base", $sformatf("\n\tDIRECTED (%s) STIMULUS DONE", mode_name),
                  UVM_LOW);

        phase.drop_objection(this, "End of directed test");
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass


class directed_test_register extends directed_test_base;
    `uvm_component_utils(test::directed_test_register)

    function new(string name, uvm_component parent);
        super.new(name, parent);
        mode_name = "register";
    endfunction
endclass


class directed_test_logic extends directed_test_base;
    `uvm_component_utils(test::directed_test_logic)

    function new(string name, uvm_component parent);
        super.new(name, parent);
        mode_name = "logic";
    endfunction
endclass
