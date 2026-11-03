// test.sv: Common test base and the default delay test
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

// ============================================================================
// Common part of all tests: environment, virtual sequence start and drain
// ============================================================================
virtual class base_test extends uvm_test;

    env_t m_env;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m_env = env_t::type_id::create("m_env", this);
    endfunction

    // Wait (bounded) until all `expected` packets have been received by the
    // model, matched by BOTH comparers and nothing is pending.
    //
    // Waiting only for an empty scoreboard is not enough: it can look empty
    // between two packets while the last packet is still on its way through
    // the RX monitors to the model.
    task drain(string who, int unsigned expected, int unsigned max_ticks);
        for (int unsigned tick = 0;
             (m_env.m_scoreboard.received_count() < expected) ||
             (m_env.m_scoreboard.compared_count() < expected) ||
             m_env.m_scoreboard.used();
             tick++) begin
            if (tick == max_ticks) begin
                `uvm_error(get_type_name(), $sformatf(
                    "Drain timeout (%s) after %0t: model received %0d/%0d, matched data %0d meta %0d, pending %0d\n%s",
                    who, max_ticks * DRAIN_TICK, m_env.m_scoreboard.received_count(), expected,
                    m_env.m_scoreboard.data_cmp.compared, m_env.m_scoreboard.meta_cmp.compared,
                    m_env.m_scoreboard.used(), m_env.m_scoreboard.data_cmp.info(1)))
                break;
            end
            #(DRAIN_TICK);
        end
        `uvm_info(get_type_name(), $sformatf("Drain (%s) done: %0d packets matched", who, expected), UVM_LOW)
    endtask

endclass

// ============================================================================
// test::delay_test - paced traffic, checks data, metadata and the exact
// release time of every packet
// ============================================================================
class delay_test extends base_test;
    `uvm_component_utils(test::delay_test)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        virt_sequence m_vseq;

        phase.raise_objection(this);

        m_vseq = virt_sequence::type_id::create("m_vseq");
        m_vseq.start(m_env.vscr);

        drain("delay", m_vseq.packet_count, DELAY_DRAIN_TICKS);

        phase.drop_objection(this);
    endtask

endclass
