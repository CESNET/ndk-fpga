// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2022-2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class data_comparer #(int unsigned ITEM_WIDTH) extends uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH));
    `uvm_component_param_utils(uvm_tx_dma_calypte::data_comparer #(ITEM_WIDTH))

    function new(string name = "uvm_tx_dma_calypte.data_comparer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function string message(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH) tr_model, uvm_logic_vector_array::sequence_item #(ITEM_WIDTH) tr_dut);
        string msg = "";
        int unsigned newline_break_cntr = 0;
        int unsigned last_wrong_byte_idx = 0;

        msg = $sformatf("%s\n\tDUT PACKET %s\n\n", msg, tr_dut.convert2string());
        msg = $sformatf("%s\n\tMODEL PACKET%s\n",  msg, tr_model.convert2string());

        msg = $sformatf("%s\n\tWRONG_BYTES:\n",  msg);

        if (tr_model.data.size() != tr_dut.data.size()) begin
            msg = $sformatf("%s\tTransaction lengths match: NO (MODEL: %0d, DUT: %0d)\n. \tUnable to compare!\n", msg, tr_model.data.size(), tr_dut.data.size());
        end else begin
            msg = $sformatf("%s\tTransaction lengths match: YES\n", msg);
            msg = $sformatf("%s\t", msg);

            foreach (tr_dut.data[it]) begin
                if (tr_dut.data[it] != tr_model.data[it]) begin
                    if (last_wrong_byte_idx != (it -1))
                        msg = $sformatf("%s\n\n\t", msg);

                    msg = $sformatf("%s%0d: (%2h, %2h), ", msg, it, tr_dut.data[it], tr_model.data[it]);
                    newline_break_cntr++;
                    last_wrong_byte_idx = it;

                    if (newline_break_cntr >= 10) begin
                        msg = $sformatf("%s\n\t", msg);
                        newline_break_cntr = 0;
                    end

                end
            end
        end

        return msg;
    endfunction
endclass

class scoreboard #(
    int unsigned USR_MFB_ITEM_WIDTH,
    int unsigned PCIE_CQ_MFB_ITEM_WIDTH,
    int unsigned CHANNELS,
    int unsigned DATA_POINTER_WIDTH,
    int unsigned USR_MFB_META_WIDTH,
    string       DEVICE
) extends uvm_scoreboard;

    `uvm_component_param_utils(uvm_tx_dma_calypte::scoreboard #(USR_MFB_ITEM_WIDTH, PCIE_CQ_MFB_ITEM_WIDTH, CHANNELS, DATA_POINTER_WIDTH, USR_MFB_META_WIDTH, DEVICE))

    //INPUT TO DUT
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(PCIE_CQ_MFB_ITEM_WIDTH))          m_pcie_cq_data_analysis_export;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)) m_pcie_cq_meta_analysis_export;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(1))                                     m_pkt_drop_analysis_export;

    //DUT OUTPUT
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(USR_MFB_ITEM_WIDTH)) m_usr_data_analysis_export;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(USR_MFB_META_WIDTH))       m_usr_meta_analysis_export;

    model #(USR_MFB_ITEM_WIDTH, PCIE_CQ_MFB_ITEM_WIDTH, CHANNELS, DATA_POINTER_WIDTH, USR_MFB_META_WIDTH, DEVICE) m_model;

    local uvm_tx_dma_calypte_regs::regmodel_top #(CHANNELS)                                     m_regmodel_top;
    data_comparer #(USR_MFB_ITEM_WIDTH)                                                         m_data_cmp;
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(USR_MFB_META_WIDTH))       m_meta_cmp;

    uvm_reg_data_t pkt_cnt          [CHANNELS];
    uvm_reg_data_t byte_cnt         [CHANNELS];
    uvm_reg_data_t discard_pkt_cnt  [CHANNELS];
    uvm_reg_data_t discard_byte_cnt [CHANNELS];
    uvm_status_e   status_r;

    local uvm_common::stats  m_delay;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        m_usr_data_analysis_export     = new("m_usr_data_analysis_export", this);
        m_usr_meta_analysis_export     = new("m_usr_meta_analysis_export", this);
        m_pcie_cq_data_analysis_export = new("m_pcie_cq_data_analysis_export", this);
        m_pcie_cq_meta_analysis_export = new("m_pcie_cq_meta_analysis_export", this);
        m_pkt_drop_analysis_export     = new("m_pkt_drop_analysis_export", this);

        //LOCAL VARIABLES
        m_delay        = new();
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_model.used() != 0);
        ret |= (m_data_cmp.used() != 0);
        ret |= (m_meta_cmp.used() != 0);
        return ret;
    endfunction

    function void regmodel_set(uvm_tx_dma_calypte_regs::regmodel_top#(CHANNELS) m_regmodel);
        this.m_regmodel_top = m_regmodel;
        m_model.regmodel_set(m_regmodel);
    endfunction

    //build phase
    function void build_phase(uvm_phase phase);
        m_model    = model #(USR_MFB_ITEM_WIDTH, PCIE_CQ_MFB_ITEM_WIDTH, CHANNELS, DATA_POINTER_WIDTH, USR_MFB_META_WIDTH, DEVICE)::type_id::create("m_model",    this);
        m_data_cmp = data_comparer #(USR_MFB_ITEM_WIDTH)                                                                          ::type_id::create("m_data_cmp", this);
        m_meta_cmp = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(USR_MFB_META_WIDTH))                        ::type_id::create("m_meta_cmp", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        m_pcie_cq_data_analysis_export.connect(m_model.m_cq_data_analysis_fifo.analysis_export);
        m_pcie_cq_meta_analysis_export.connect(m_model.m_cq_meta_analysis_fifo.analysis_export);

        m_model.m_usr_data_analysis_port.connect(m_data_cmp.analysis_imp_model);
        m_model.m_usr_meta_analysis_port.connect(m_meta_cmp.analysis_imp_model);

        m_usr_data_analysis_export.connect(m_data_cmp.analysis_imp_dut);
        m_usr_meta_analysis_export.connect(m_meta_cmp.analysis_imp_dut);
        m_pkt_drop_analysis_export.connect(m_model.m_discard_comp.m_internal_meta_analysis_fifo.analysis_export);
    endfunction

    function void print_counters(ref string msg, input string cntr_name, int unsigned dut_cntr, int unsigned model_cntr);
        msg = {msg, $sformatf("%s\n", cntr_name)};
        msg = {msg, $sformatf("DUT:   %0d\n", dut_cntr)};
        msg = {msg, $sformatf("MODEL: %0d\n", model_cntr)};
        msg = {msg, $sformatf("--------------------\n")};
        msg = {msg, $sformatf("DIFF:  %0d\n", dut_cntr - model_cntr)};
    endfunction

    function void report_phase(uvm_phase phase);
        real min;
        real max;
        real avg;
        real std_dev;
        real median;
        real modus;
        int unsigned match_flag = 1;
        string msg = "\n";

        if (this.get_report_verbosity_level() >= UVM_LOW) begin
            m_delay.count(min, max, avg, std_dev);
            msg = {msg, $sformatf("\tDelay statistic (SOF to SOF) => min : %0dns, max : %0dns, average : %0dns, standard deviation : %0dns, median : %0dns, modus : %0dns\n", min, max, avg, std_dev, median, modus)};
        end

        for (int chan = 0; chan < CHANNELS; chan++) begin

            msg = {msg, $sformatf("\n=================================================================================\n")};
            msg = {msg, $sformatf("CHANNEL %0d\n", chan)};
            msg = {msg, $sformatf("=================================================================================\n")};

            if (byte_cnt[chan] != m_model.m_channel_info[chan].dma_transactions_bytes &&
                pkt_cnt[chan]  != m_model.m_channel_info[chan].dma_transactions &&
                discard_byte_cnt[chan] != m_model.m_channel_info[chan].drop_transactions_bytes &&
                discard_pkt_cnt[chan]  != m_model.m_channel_info[chan].drop_transactions) begin

                msg = {msg, $sformatf("Packet counters DO NOT match!\n")};
                match_flag &= 0;

            end else begin
                msg = {msg, $sformatf("Packet counters match!\n")};
                match_flag &= 1;
            end

            if (pkt_cnt[chan]  != m_model.m_channel_info[chan].dma_transactions)
                print_counters(msg, "SEND_PACKETS",    pkt_cnt[chan],          m_model.m_channel_info[chan].dma_transactions);

            if (byte_cnt[chan] != m_model.m_channel_info[chan].dma_transactions_bytes)
                print_counters(msg, "SEND_BYTES",      byte_cnt[chan],         m_model.m_channel_info[chan].dma_transactions_bytes);

            if (discard_pkt_cnt[chan] != m_model.m_channel_info[chan].drop_transactions)
                print_counters(msg, "DISCARD_PACKETS", discard_pkt_cnt[chan],  m_model.m_channel_info[chan].drop_transactions);

            if (discard_byte_cnt[chan] != m_model.m_channel_info[chan].drop_transactions_bytes)
                print_counters(msg, "DISCARD_BYTES",   discard_byte_cnt[chan], m_model.m_channel_info[chan].drop_transactions_bytes);

            msg = {msg, $sformatf("\n----MODEL COUNTERS----\n"                                                   )};
            msg = {msg, $sformatf("PKT_CNT            %d\n", m_model.m_channel_info[chan].dma_transactions       )};
            msg = {msg, $sformatf("BYTE_CNT           %d\n", m_model.m_channel_info[chan].dma_transactions_bytes )};
            msg = {msg, $sformatf("DISCARD_PKT_CNT    %d\n", m_model.m_channel_info[chan].drop_transactions      )};
            msg = {msg, $sformatf("DISCARD_BYTE_CNT   %d\n", m_model.m_channel_info[chan].drop_transactions_bytes)};

            msg = {msg, $sformatf("\n----DUT COUNTERS----\n"                       )};
            msg = {msg, $sformatf("PKT_CNT            %d\n", pkt_cnt[chan]         )};
            msg = {msg, $sformatf("BYTE_CNT           %d\n", byte_cnt[chan]        )};
            msg = {msg, $sformatf("DISCARD_PKT_CNT    %d\n", discard_pkt_cnt[chan] )};
            msg = {msg, $sformatf("DISCARD_BYTE_CNT   %d\n", discard_byte_cnt[chan])};
        end

        msg = {msg, $sformatf("=================================================================================\n")};

        if (this.used() == 0 && match_flag == 1) begin

            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            string msg = "";
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAILED       ----\n\t---------------------------------------"}, UVM_NONE)
        end
    endfunction
endclass
