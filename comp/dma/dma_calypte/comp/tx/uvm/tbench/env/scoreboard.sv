// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2022-2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Reason for the reimplemenation of the comparer: A need for a custom print function when the transactions are
// not equal
class data_comparer #(int unsigned ITEM_WIDTH) extends
    uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH));
    `uvm_component_param_utils(uvm_tx_dma_calypte::data_comparer #(ITEM_WIDTH))

    function new(string name = "uvm_tx_dma_calypte.data_comparer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function string message(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH) tr_model,
                                    uvm_logic_vector_array::sequence_item #(ITEM_WIDTH) tr_dut);
        string msg = "";
        int unsigned newline_break_cntr = 0;
        int unsigned last_wrong_byte_idx = 0;

        msg = $sformatf("%s\nByte comparison:\n", msg);

        if (tr_model.data.size() != tr_dut.data.size()) begin
            msg = $sformatf("%s\n\tTransaction lengths match: NO (MODEL: %0d, DUT: %0d)\n. \tUnable to compare!\n",
                            msg, tr_model.data.size(), tr_dut.data.size());
        end else begin
            msg = $sformatf("%s\n\tTransaction lengths match: YES\n", msg);
            msg = $sformatf("%s\n\tWRONG_BYTES:\n",  msg);

            foreach (tr_dut.data[it]) begin
                // msg = $sformatf("%s%0d: (%2h, %2h), \n", msg, it, tr_dut.data[it], tr_model.data[it]);
                if (tr_dut.data[it] !== tr_model.data[it]) begin
                    if (last_wrong_byte_idx != (it -1)) begin
                        msg = $sformatf("%s\n\n\t", msg);
                    end

                    msg = $sformatf("%s%0d: (%2h, %2h), ", msg, it, tr_dut.data[it], tr_model.data[it]);
                    newline_break_cntr++;
                    last_wrong_byte_idx = it;

                    if (newline_break_cntr >= 10) begin
                        msg = $sformatf("%s\n\t", msg);
                        newline_break_cntr = 0;
                    end
                end
            end
            msg = $sformatf("%s\n", msg);
        end

        return msg;
    endfunction

    virtual function int unsigned compare(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH) tr_model,
                                          uvm_logic_vector_array::sequence_item #(ITEM_WIDTH) tr_dut);

        int unsigned comp_res = tr_model.compare(tr_dut);

        if (comp_res == 0) begin
            `uvm_info(this.get_full_name(), this.message(tr_model, tr_dut), UVM_LOW);
        end

        return comp_res;
    endfunction
endclass

class ptr_upd_data_parser #(
    int unsigned PCIE_CQ_MFB_ITEM_WIDTH,
    string DEVICE
) extends uvm_component;

    `uvm_component_param_utils(uvm_tx_dma_calypte::ptr_upd_data_parser #(PCIE_CQ_MFB_ITEM_WIDTH, DEVICE))

    localparam MPS          = 256;
    localparam PAGE_SIZE    = 4096;
    localparam IS_INTEL_DEV = (DEVICE == "STRATIX10" || DEVICE == "AGILEX");

    // Input FIFOs
    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item
                            #(PCIE_CQ_MFB_ITEM_WIDTH))                  m_ptr_upd_mfb_data_fifo;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item
                            #(sv_pcie_meta_pack::PCIE_RQ_META_WIDTH))   m_ptr_upd_mfb_meta_fifo;

    // Output port with parsed data to PCIe Requester transaction
    uvm_analysis_port #(uvm_pcie::request_header)                       m_ptr_upd_pcie_port;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        m_ptr_upd_mfb_data_fifo = new("m_ptr_upd_mfb_data_fifo", this);
        m_ptr_upd_mfb_meta_fifo = new("m_ptr_upd_mfb_meta_fifo", this);
        m_ptr_upd_pcie_port     = new("m_ptr_upd_pcie_port", this);
    endfunction

    task run_phase(uvm_phase phase);
        bit                                                                      ret = 1;
        uvm_logic_vector_array::sequence_item #(PCIE_CQ_MFB_ITEM_WIDTH)          dut_in_tr_data;
        uvm_logic_vector::sequence_item #(sv_pcie_meta_pack::PCIE_RQ_META_WIDTH) dut_in_tr_meta;
        uvm_pcie::request_header                                                 dut_out_tr;

        forever begin
            m_ptr_upd_mfb_data_fifo.get(dut_in_tr_data);
            m_ptr_upd_mfb_meta_fifo.get(dut_in_tr_meta);

            dut_out_tr = uvm_pcie::request_header::type_id::create(this.get_full_name);

            if (IS_INTEL_DEV) begin // Intel P/R-Tile
                logic tag9;
                logic tag8;
                logic ln;

                {dut_out_tr.fmt,
                 dut_out_tr.pcie_type,
                 tag9,
                 dut_out_tr.traffic_class,
                 tag8,
                 dut_out_tr.id_based_ordering,
                 ln,
                 dut_out_tr.th,
                 dut_out_tr.td,
                 dut_out_tr.ep,
                 dut_out_tr.relaxed_ordering,
                 dut_out_tr.no_snoop,
                 dut_out_tr.at,
                 dut_out_tr.length} = dut_in_tr_meta.data[32-1 -: 32];

                if (dut_out_tr.fmt[0] == 1'b0) begin
                    dut_out_tr.address[64-1:32] = 0;

                    {dut_out_tr.requester_id,
                     dut_out_tr.tag,
                     dut_out_tr.lbe,
                     dut_out_tr.fbe,
                     dut_out_tr.address[32-1:2],
                     dut_out_tr.ph} = {dut_in_tr_meta.data[64-1 -: 32],
                                       dut_in_tr_meta.data[96-1 -: 32]};
                end else begin
                    {dut_out_tr.requester_id,
                     dut_out_tr.tag,
                     dut_out_tr.lbe,
                     dut_out_tr.fbe,
                     dut_out_tr.address,
                     dut_out_tr.ph} = {dut_in_tr_meta.data[64-1 -: 32],
                                       dut_in_tr_meta.data[96-1 -: 32],
                                       dut_in_tr_meta.data[128-1 -: 32]};
                end

                if ({dut_out_tr.fmt, dut_out_tr.pcie_type} != 8'b01100000
                    && {dut_out_tr.fmt, dut_out_tr.pcie_type} != 8'b01000000) begin
                    `uvm_error(this.get_full_name(),
                               $sformatf("\nUnsupporte request\n\tfmt : 0x%h\n\ttype : 0x%h\n", dut_out_tr.fmt,
                                         dut_out_tr.pcie_type));
                end

                ret &= tag9 === 0;
                ret &= tag8 === 0;
                ret &= ln === 0;

                if (ret == 0) begin
                    `uvm_error(this.get_full_name(),
                               $sformatf("\nThese fields should be 0: tag8: %b, tag9: %b, ln: %b", tag8, tag9, ln));
                end

                dut_out_tr.data = dut_in_tr_data.data;

            end else begin // AMD FPGA
                logic [16-1:0] cptr_id; //compleater ID
                logic [1-1:0]  rq_id_enabled;
                logic [4-1:0]  rq_type;
                logic [1-1:0]  dummy_length;

                {dut_out_tr.td,
                 dut_out_tr.id_based_ordering,
                 dut_out_tr.relaxed_ordering,
                 dut_out_tr.no_snoop,
                 dut_out_tr.traffic_class,
                 rq_id_enabled,
                 cptr_id,
                 dut_out_tr.tag,
                 dut_out_tr.requester_id,
                 dut_out_tr.ep,
                 rq_type,
                 dummy_length,
                 dut_out_tr.length,
                 dut_out_tr.address,
                 dut_out_tr.at} = {dut_in_tr_data.data[3],
                                   dut_in_tr_data.data[2],
                                   dut_in_tr_data.data[1],
                                   dut_in_tr_data.data[0]};

                dut_out_tr.data = new[dut_in_tr_data.data.size() -4];

                for (int unsigned it = 0; it < dut_in_tr_data.data.size() -4; it++) begin
                    dut_out_tr.data[it] = dut_in_tr_data.data[it+4];
                end

                dut_out_tr.th         = 0;
                dut_out_tr.fbe        = dut_in_tr_meta.data[164-1 : 160];
                dut_out_tr.lbe        = dut_in_tr_meta.data[168-1 : 164];
                dut_out_tr.ph         = 0;
                dut_out_tr.fmt        = dut_out_tr.address[64-1:32] != 0 ? 3'b011 : 3'b010;
                dut_out_tr.pcie_type  = 5'b00000;

                ret &= rq_type === 4'h1;
                ret &= rq_id_enabled === 0;
                ret &= cptr_id === 0;
                ret &= dummy_length === 0;

                if (ret == 0) begin
                    `uvm_error(this.get_full_name(),
                               $sformatf({"\nThese fields should be 0: rq_type: %b, rq_id_enabled: %b, ",
                                          "cptr_id: %b, dummy_length: %b"},
                                         rq_type, rq_id_enabled, cptr_id, dummy_length));
                end
            end

            if (dut_out_tr.data.size() > MPS
                || (((dut_out_tr.address & (PAGE_SIZE-1)) + dut_out_tr.data.size()) > PAGE_SIZE)) begin

                string err_msg = $sformatf("\n\tPacket doesn't meet pcie requirements.");
                err_msg = {err_msg, $sformatf("\n\t\tPacket size %0d", dut_out_tr.data.size())};
                err_msg = {err_msg, $sformatf("\n\t\tMaximum payload(%0d) exceeded %0d", MPS,
                                              dut_out_tr.data.size() > MPS)};
                err_msg = {err_msg,
                           $sformatf("\n\t\tPage(%0d) boundary exceeded %0d addr 0x%h", PAGE_SIZE,
                                     (((dut_out_tr.address & (PAGE_SIZE-1)) + dut_out_tr.data.size()) > PAGE_SIZE),
                                     dut_out_tr.address)};
                `uvm_error(this.get_full_name(), err_msg);
            end

            dut_out_tr.time_add("ptr_upd_data_parser", $time());
            m_ptr_upd_pcie_port.write(dut_out_tr);
        end
    endtask
endclass

class scoreboard #(
    int unsigned USR_MFB_ITEM_WIDTH,
    int unsigned PCIE_CQ_MFB_ITEM_WIDTH,
    int unsigned CHANNELS,
    int unsigned DATA_POINTER_WIDTH,
    int unsigned USR_MFB_META_WIDTH,
    string       DEVICE,
    int unsigned UPD_THRESHOLD
) extends uvm_scoreboard;

    `uvm_component_param_utils(uvm_tx_dma_calypte::scoreboard #(USR_MFB_ITEM_WIDTH, PCIE_CQ_MFB_ITEM_WIDTH, CHANNELS,
                                                                DATA_POINTER_WIDTH, USR_MFB_META_WIDTH, DEVICE,
                                                                UPD_THRESHOLD))

    localparam UPD_STOP_REQ_MVB_ITEM_W = (DATA_POINTER_WIDTH-3) + DATA_POINTER_WIDTH + 1 + 64;
    localparam RT_UPD_MVB_ITEM_W       = (DATA_POINTER_WIDTH-3) + DATA_POINTER_WIDTH + $clog2(CHANNELS);

    // ------------------------------------------------------------------
    //INPUT TO DUT
    // ------------------------------------------------------------------
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item
                          #(PCIE_CQ_MFB_ITEM_WIDTH))                m_pcie_cq_data_exp;
    uvm_analysis_export #(uvm_logic_vector::sequence_item
                          #(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)) m_pcie_cq_meta_exp;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(1))     m_pkt_drop_exp;

    // ------------------------------------------------------------------
    // DUT OUTPUT
    // ------------------------------------------------------------------
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(USR_MFB_ITEM_WIDTH)) m_usr_data_exp;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(USR_MFB_META_WIDTH))       m_usr_meta_exp;

    // ------------------------------------------------------------------
    // Pointer updater interfaces
    // ------------------------------------------------------------------
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(PCIE_CQ_MFB_ITEM_WIDTH)) m_ptr_upd_mfb_data_exp;
    uvm_analysis_export #(uvm_logic_vector::sequence_item
                          #(sv_pcie_meta_pack::PCIE_RQ_META_WIDTH))                        m_ptr_upd_mfb_meta_exp;

    uvm_analysis_export #(uvm_logic_vector::sequence_item #(UPD_STOP_REQ_MVB_ITEM_W)) m_upd_stop_req_mvb_exp;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #($clog2(CHANNELS)))        m_chan_start_req_mvb_exp;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(RT_UPD_MVB_ITEM_W))       m_rt_upd_req_mvb_exp;

    local dma_model #(USR_MFB_ITEM_WIDTH, PCIE_CQ_MFB_ITEM_WIDTH, CHANNELS, DATA_POINTER_WIDTH, USR_MFB_META_WIDTH,
                      DEVICE)                                                                m_dma_model;
    local ptr_updater_model #(DATA_POINTER_WIDTH, CHANNELS, UPD_THRESHOLD)                   m_ptr_upd_model;

    data_comparer #(USR_MFB_ITEM_WIDTH)                                                   m_data_cmp;
    uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(USR_MFB_META_WIDTH)) m_meta_cmp;

    local ptr_upd_data_parser #(PCIE_CQ_MFB_ITEM_WIDTH, DEVICE) m_ptr_upd_data_prs;
    uvm_common::comparer_unordered #(uvm_pcie::request_header)  m_ptr_upd_cmp;

    uvm_reg_data_t pkt_cnt          [CHANNELS];
    uvm_reg_data_t byte_cnt         [CHANNELS];
    uvm_reg_data_t discard_pkt_cnt  [CHANNELS];
    uvm_reg_data_t discard_byte_cnt [CHANNELS];
    uvm_status_e   status_r;

    local uvm_common::stats  m_delay;

    local int unsigned m_ptr_upd_tr_compared = 0;
    local int unsigned m_ptr_upd_tr_errors   = 0;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        m_usr_data_exp           = new("m_usr_data_exp", this);
        m_usr_meta_exp           = new("m_usr_meta_exp", this);
        m_pcie_cq_data_exp       = new("m_pcie_cq_data_exp", this);
        m_pcie_cq_meta_exp       = new("m_pcie_cq_meta_exp", this);
        m_pkt_drop_exp           = new("m_pkt_drop_exp", this);
        m_ptr_upd_mfb_data_exp   = new("m_ptr_upd_mfb_data_exp", this);
        m_ptr_upd_mfb_meta_exp   = new("m_ptr_upd_mfb_meta_exp", this);
        m_upd_stop_req_mvb_exp   = new("m_upd_stop_req_mvb_exp", this);
        m_chan_start_req_mvb_exp = new("m_chan_start_req_mvb_exp", this);
        m_rt_upd_req_mvb_exp     = new("m_rt_upd_req_mvb_exp", this);
        m_delay                  = new();
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_dma_model.used() != 0);
        ret |= (m_ptr_upd_model.used() != 0);
        ret |= (m_data_cmp.used() != 0);
        ret |= (m_meta_cmp.used() != 0);
        return ret;
    endfunction

    function void regmodel_set(uvm_tx_dma_calypte_regs::regmodel_top #(CHANNELS, DATA_POINTER_WIDTH) m_regmodel);
        m_ptr_upd_model.regmodel_set(m_regmodel);
    endfunction

    //build phase
    function void build_phase(uvm_phase phase);
        m_dma_model    = dma_model #(USR_MFB_ITEM_WIDTH, PCIE_CQ_MFB_ITEM_WIDTH, CHANNELS, DATA_POINTER_WIDTH,
                                     USR_MFB_META_WIDTH, DEVICE)::type_id::create("m_dma_model",    this);
        m_ptr_upd_model = ptr_updater_model #(DATA_POINTER_WIDTH, CHANNELS, UPD_THRESHOLD)::type_id
                          ::create("m_ptr_upd_model", this);
        m_data_cmp = data_comparer #(USR_MFB_ITEM_WIDTH)::type_id::create("m_data_cmp", this);
        m_meta_cmp = uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item #(USR_MFB_META_WIDTH))::type_id
                     ::create("m_meta_cmp", this);
        m_ptr_upd_data_prs = ptr_upd_data_parser #(PCIE_CQ_MFB_ITEM_WIDTH, DEVICE)::type_id
                             ::create("m_ptr_upd_data_prs", this);
        m_ptr_upd_cmp = uvm_common::comparer_unordered #(uvm_pcie::request_header)::type_id
                        ::create("m_ptr_upd_cmp", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        m_pcie_cq_data_exp.connect(m_dma_model.m_cq_data_analysis_fifo.analysis_export);
        m_pcie_cq_meta_exp.connect(m_dma_model.m_cq_meta_analysis_fifo.analysis_export);
        m_dma_model.m_usr_data_analysis_port.connect(m_data_cmp.analysis_imp_model);
        m_dma_model.m_usr_meta_analysis_port.connect(m_meta_cmp.analysis_imp_model);
        m_usr_data_exp.connect(m_data_cmp.analysis_imp_dut);
        m_usr_meta_exp.connect(m_meta_cmp.analysis_imp_dut);
        m_pkt_drop_exp.connect(m_dma_model.m_discard_comp.m_internal_meta_analysis_fifo.analysis_export);

        m_ptr_upd_mfb_data_exp.connect(m_ptr_upd_data_prs.m_ptr_upd_mfb_data_fifo.analysis_export);
        m_ptr_upd_mfb_meta_exp.connect(m_ptr_upd_data_prs.m_ptr_upd_mfb_meta_fifo.analysis_export);
        m_upd_stop_req_mvb_exp.connect(m_ptr_upd_model.m_upd_stop_req_fifo.analysis_export);
        m_chan_start_req_mvb_exp.connect(m_ptr_upd_model.m_chan_start_req_fifo.analysis_export);
        m_rt_upd_req_mvb_exp.connect(m_ptr_upd_model.m_rt_upd_req_fifo.analysis_export);
        m_ptr_upd_data_prs.m_ptr_upd_pcie_port.connect(m_ptr_upd_cmp.analysis_imp_dut);
        m_ptr_upd_model.m_ptr_upd_pcie_port.connect(m_ptr_upd_cmp.analysis_imp_model);
    endfunction

    function void print_counters(ref string   msg, input string cntr_name, int unsigned dut_cntr,
                                 int unsigned model_cntr);
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
            msg = {msg, $sformatf({"\tDelay statistic (SOF to SOF) => min : %0dns, max : %0dns, average : %0dns, ",
                                  "standard deviation : %0dns, median : %0dns, modus : %0dns\n"}, min, max, avg,
                                  std_dev, median, modus)};
        end

        for (int chan = 0; chan < CHANNELS; chan++) begin

            msg = {msg, $sformatf(
                "\n=================================================================================\n")};
            msg = {msg, $sformatf("CHANNEL %0d\n", chan)};
            msg = {msg, $sformatf(
                "=================================================================================\n")};

            if (byte_cnt[chan] != m_dma_model.m_channel_info[chan].dma_transactions_bytes &&
                pkt_cnt[chan]  != m_dma_model.m_channel_info[chan].dma_transactions &&
                discard_byte_cnt[chan] != m_dma_model.m_channel_info[chan].drop_transactions_bytes &&
                discard_pkt_cnt[chan]  != m_dma_model.m_channel_info[chan].drop_transactions) begin

                msg = {msg, $sformatf("Packet counters DO NOT match!\n")};
                match_flag &= 0;

            end else begin
                msg = {msg, $sformatf("Packet counters match!\n")};
                match_flag &= 1;
            end

            if (pkt_cnt[chan]  != m_dma_model.m_channel_info[chan].dma_transactions) begin
                print_counters(msg, "SEND_PACKETS",    pkt_cnt[chan],
                               m_dma_model.m_channel_info[chan].dma_transactions);
            end

            if (byte_cnt[chan] != m_dma_model.m_channel_info[chan].dma_transactions_bytes) begin
                print_counters(msg, "SEND_BYTES",      byte_cnt[chan],
                               m_dma_model.m_channel_info[chan].dma_transactions_bytes);
            end

            if (discard_pkt_cnt[chan] != m_dma_model.m_channel_info[chan].drop_transactions) begin
                print_counters(msg, "DISCARD_PACKETS", discard_pkt_cnt[chan],
                               m_dma_model.m_channel_info[chan].drop_transactions);
            end

            if (discard_byte_cnt[chan] != m_dma_model.m_channel_info[chan].drop_transactions_bytes) begin
                print_counters(msg, "DISCARD_BYTES",   discard_byte_cnt[chan],
                               m_dma_model.m_channel_info[chan].drop_transactions_bytes);
            end

            msg = {msg, $sformatf("\n----MODEL COUNTERS----\n"                                                       )};
            msg = {msg, $sformatf("PKT_CNT            %d\n", m_dma_model.m_channel_info[chan].dma_transactions       )};
            msg = {msg, $sformatf("BYTE_CNT           %d\n", m_dma_model.m_channel_info[chan].dma_transactions_bytes )};
            msg = {msg, $sformatf("DISCARD_PKT_CNT    %d\n", m_dma_model.m_channel_info[chan].drop_transactions      )};
            msg = {msg, $sformatf("DISCARD_BYTE_CNT   %d\n", m_dma_model.m_channel_info[chan].drop_transactions_bytes)};

            msg = {msg, $sformatf("\n----DUT COUNTERS----\n"                       )};
            msg = {msg, $sformatf("PKT_CNT            %d\n", pkt_cnt[chan]         )};
            msg = {msg, $sformatf("BYTE_CNT           %d\n", byte_cnt[chan]        )};
            msg = {msg, $sformatf("DISCARD_PKT_CNT    %d\n", discard_pkt_cnt[chan] )};
            msg = {msg, $sformatf("DISCARD_BYTE_CNT   %d\n", discard_byte_cnt[chan])};
        end

        msg = {msg, $sformatf("=================================================================================\n")};

        if (this.used() == 0 && match_flag == 1 && m_ptr_upd_tr_errors == 0) begin

            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     ",
                                        "VERIFICATION SUCCESS      ----\n\t---------------------------------------"},
                      UVM_NONE)
        end else begin
            string msg = "";
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     ",
                                        "VERIFICATION FAILED       ----\n\t---------------------------------------"},
                      UVM_NONE)
        end
    endfunction
endclass
