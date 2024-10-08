// sequence.sv: Virtual sequence
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>
//            Vladislav Válek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_simple extends uvm_sequence#(uvm_tx_dma_calypte_cq::sequence_item);
    `uvm_object_param_utils(uvm_tx_dma_calypte::sequence_simple)
    `uvm_declare_p_sequencer(uvm_tx_dma_calypte_cq::sequencer)

    int unsigned m_packet_size_min = 60;
    int unsigned m_packet_size_max = 2048;

    function new(string name = "uvm_tx_dma_calypte::sequence_simple");
        super.new(name);
    endfunction

    task send_packets(uvm_common::sequence_cfg m_state, int unsigned min, int unsigned max);
        int unsigned it;
        int unsigned transaction_count;

        std::randomize(transaction_count) with {
            transaction_count dist {[1:100] :/ 10, [100:1000] :/ 20, [1000:5000] :/ 60, [5000:50000] :/ 10};
            transaction_count >= min;
            transaction_count <= max;
        };

        //RUN DATA
        it = 0;
        while(it < transaction_count && (m_state == null || m_state.next())) begin
            start_item(req);
            assert(req.randomize() with {req.m_packet.size() inside {[m_packet_size_min:m_packet_size_max-1]};}) else `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize packet");
            finish_item(req);

            it++;
        end
    endtask

    task body();
        uvm_common::sequence_cfg                   m_state;
        uvm_tx_dma_calypte_regs::start_channel_seq m_start_chan_seq;
        uvm_tx_dma_calypte_regs::stop_channel_seq  m_stop_chan_seq;

        m_start_chan_seq = uvm_tx_dma_calypte_regs::start_channel_seq::type_id::create("m_start_chan_seq", m_sequencer);
        m_stop_chan_seq  = uvm_tx_dma_calypte_regs::stop_channel_seq ::type_id::create("m_stop_chan_seq",  m_sequencer);
        m_start_chan_seq.m_regmodel_channel = p_sequencer.m_regmodel_channel;
        m_stop_chan_seq.m_regmodel_channel  = p_sequencer.m_regmodel_channel;

        req = uvm_tx_dma_calypte_cq::sequence_item::type_id::create("req", m_sequencer);

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", m_state)) begin
            m_state = null;
        end

        m_start_chan_seq.start(null);

        while(m_state == null || !m_state.stopped()) begin
            send_packets(m_state, 1, 500);
            m_stop_chan_seq.start(null);
            send_packets(m_state, 1, 500);
            m_start_chan_seq.start(null);
        end

        m_stop_chan_seq.start(null);
    endtask
endclass
