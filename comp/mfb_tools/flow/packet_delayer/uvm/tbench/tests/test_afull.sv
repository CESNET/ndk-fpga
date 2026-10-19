// test_afull.sv: FIFO almost-full / almost-empty (PAUSE_REQUEST) test
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

// test::afull_test - a continuous RX flood fills the RX FIFO to FIFO_AFULL
// (PAUSE_REQUEST rises); after the stimulus it drains to FIFO_AEMPTY
// (PAUSE_REQUEST falls). Checks both PAUSE_REQUEST edges and bit-exact
// data/metadata. The time check is disabled: under overload the release is
// back-pressure driven, not timestamp driven.
class afull_test extends base_test;
    `uvm_component_utils(test::afull_test)

    pause_checker m_pause_checker;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        // Flood: no gaps between packets, SRC_RDY always high
        uvm_config_db#(int unsigned)::set(this, "*", "rx_space_size_min",      0);
        uvm_config_db#(int unsigned)::set(this, "*", "rx_space_size_max",      0);
        uvm_config_db#(int unsigned)::set(this, "*", "rx_rdy_probability_min", 100);
        uvm_config_db#(int unsigned)::set(this, "*", "rx_rdy_probability_max", 100);
        // Data-only check: under overload the release is back-pressure driven
        uvm_config_db#(bit)         ::set(this, "*", "time_check_enable", 0);

        super.build_phase(phase);

        m_pause_checker = pause_checker::type_id::create("m_pause_checker", this);
    endfunction

    task run_phase(uvm_phase phase);
        virt_sequence m_vseq;
        bit           pause_ok;

        phase.raise_objection(this);

        m_vseq = virt_sequence::type_id::create("m_vseq");
        m_vseq.packet_count_min = AFULL_PACKET_COUNT_MIN;
        m_vseq.packet_count_max = AFULL_PACKET_COUNT_MAX;
        m_vseq.ts_min           = AFULL_TS_MIN;
        m_vseq.ts_max           = AFULL_TS_MAX;
        m_vseq.start(m_env.vscr);

        drain("afull", m_vseq.packet_count, AFULL_DRAIN_TICKS);

        // After the drain PAUSE_REQUEST must fall (FIFO_AEMPTY)
        m_pause_checker.wait_fall(AFULL_PAUSE_WDT, pause_ok);
        if (!pause_ok) begin
            `uvm_error(get_type_name(), $sformatf(
                "PAUSE_REQUEST did not fall within %0t after the drain: RX FIFO did not reach FIFO_AEMPTY",
                AFULL_PAUSE_WDT))
        end

        phase.drop_objection(this);
    endtask
endclass
