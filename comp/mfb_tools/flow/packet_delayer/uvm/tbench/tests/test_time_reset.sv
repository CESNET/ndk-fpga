// test_time_reset.sv: TIME_RESET (time epoch re-arm) test
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

// test::time_reset_test - two traffic phases around a TIME_RESET pulse:
//
//   phase A : reset + traffic, absolute timestamps starting at 0
//   drain   : wait until every packet of phase A has been matched
//   pulse   : TIME_RESET (re-arms the DUT epoch, applied with the next SOF)
//   phase B : traffic only, absolute timestamps re-based (start at 1)
//
// After TIME_RESET the DUT time restarts from zero, so phase B must re-base
// its timestamps (a continuation of phase A would never be released). The
// model re-anchors its epoch when it observes the pulse, so the exact time
// check stays valid across it.
//
// TIME_RESET only has an effect for TS_FORMAT = 1.
class time_reset_test extends base_test;
    `uvm_component_utils(test::time_reset_test)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        if (TS_FORMAT != 1) begin
            `uvm_fatal(get_type_name(), $sformatf(
                "test::time_reset_test requires TS_FORMAT = 1 (current %0d): %s", TS_FORMAT,
                "TIME_RESET only re-arms the epoch of absolute timestamps"))
        end
        super.build_phase(phase);
    endfunction

    // One traffic phase of PHASE_PACKET_COUNT packets
    task run_traffic(string name, bit do_reset, logic [TS_WIDTH-1:0] ts_start);
        virt_sequence m_vseq;

        m_vseq = virt_sequence::type_id::create({"m_vseq_", name});
        m_vseq.packet_count   = PHASE_PACKET_COUNT;
        m_vseq.do_reset       = do_reset;
        m_vseq.ts_start_value = ts_start;

        `uvm_info(get_type_name(), $sformatf("Phase %s: %0d packets, ts_start=%0d, reset='b%0b",
                  name, PHASE_PACKET_COUNT, ts_start, do_reset), UVM_LOW)
        m_vseq.start(m_env.vscr);
    endtask

    task run_phase(uvm_phase phase);
        uvm_reset::sequence_reset m_tr_pulse;
        uvm_reset::sequence_run   m_tr_low;

        phase.raise_objection(this);

        // Phase A: reset + traffic, timestamps from 0
        run_traffic("A", 1, '0);
        drain("A", PHASE_PACKET_COUNT, TIME_RESET_DRAIN_TICKS);

        // TIME_RESET pulse while the DUT is empty
        #(TIME_RESET_GAP_CLKS * CLK_PERIOD);
        m_tr_pulse = uvm_reset::sequence_reset::type_id::create("m_tr_pulse");
        m_tr_pulse.length_min = TIME_RESET_PULSE_CLKS;
        m_tr_pulse.length_max = TIME_RESET_PULSE_CLKS;
        void'(m_tr_pulse.randomize());
        m_tr_pulse.start(m_env.vscr.m_time_reset_sqr);
        // Back to 0 (the reset driver keeps the last level)
        m_tr_low = uvm_reset::sequence_run::type_id::create("m_tr_low");
        m_tr_low.length_min = 1;
        m_tr_low.length_max = 1;
        void'(m_tr_low.randomize());
        m_tr_low.start(m_env.vscr.m_time_reset_sqr);
        #(TIME_RESET_GAP_CLKS * CLK_PERIOD);

        // Phase B: traffic only, timestamps re-based after the pulse
        run_traffic("B", 0, 'd1);
        drain("B", 2 * PHASE_PACKET_COUNT, TIME_RESET_DRAIN_TICKS);

        // The pulse must actually have reached the DUT
        if (m_env.m_scoreboard.time_reset_count() < TIME_RESET_COUNT) begin
            `uvm_error(get_type_name(), $sformatf("TIME_RESET observed %0d time(s), expected at least %0d",
                       m_env.m_scoreboard.time_reset_count(), TIME_RESET_COUNT))
        end

        phase.drop_objection(this);
    endtask
endclass
