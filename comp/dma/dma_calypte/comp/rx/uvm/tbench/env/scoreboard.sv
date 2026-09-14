//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


// Comparer of the DUT PCIe RQ transactions against the model expectations.
//
// It is based on the uvm_common::comparer_base_ordered which pairs a model and
// a DUT transaction only when both of them are available, keeps the unpaired
// transactions in queues visible to used()/check_phase and flags the
// transactions which wait too long for their counterpart (delay watchdogs).
class pcie_rq_comparer #(type MODEL_ITEM) extends uvm_common::comparer_base_ordered #(MODEL_ITEM, uvm_pcie::header);
    `uvm_component_param_utils(uvm_dma_ll::pcie_rq_comparer #(MODEL_ITEM))

    localparam int unsigned MPS       = 256;
    localparam int unsigned PAGE_SIZE = 4096;

    // When set, the delay of the first data part of each packet is recorded
    // (used only by the DMA data comparer).
    uvm_common::stats delay_stat;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        uvm_pcie::request_header dut_rq;
        dma_model_packet         model_pkt;
        bit                      ret = 1;

        assert($cast(dut_rq, tr_dut));

        ret &= dut_rq.fmt                === tr_model.fmt;
        ret &= dut_rq.pcie_type          === tr_model.pcie_type;
        ret &= dut_rq.traffic_class      === tr_model.traffic_class;
        ret &= dut_rq.id_based_ordering  === tr_model.id_based_ordering;
        ret &= dut_rq.relaxed_ordering   === tr_model.relaxed_ordering;
        ret &= dut_rq.no_snoop           === tr_model.no_snoop;
        ret &= dut_rq.th                 === tr_model.th; // TLP Processing Hints
        ret &= dut_rq.td                 === tr_model.td;
        ret &= dut_rq.ep                 === tr_model.ep; // poisoned
        ret &= dut_rq.at                 === tr_model.at;
        ret &= dut_rq.length             === tr_model.length; //dwords
        ret &= (dut_rq.data              ==? tr_model.data) === 1'b1;
        ret &= dut_rq.requester_id       === tr_model.requester_id;
        ret &= dut_rq.tag                === tr_model.tag;
        ret &= dut_rq.lbe                === tr_model.lbe;
        ret &= dut_rq.fbe                === tr_model.fbe;
        ret &= dut_rq.address            === tr_model.address;
        ret &= dut_rq.ph                 === tr_model.ph;

        //Check pcie requiretments
        if (dut_rq.data.size() > MPS || ((({dut_rq.address, 2'b00} & (PAGE_SIZE-1)) + dut_rq.data.size()) > PAGE_SIZE)) begin
            const logic [64-1:0] tmp_addr = (({dut_rq.address, 2'b00} & (PAGE_SIZE-1)) + dut_rq.data.size());
            string err_msg = $sformatf("\n\tPacket doesn't meet pcie requirements.");
            err_msg = {err_msg, $sformatf("\n\t\tPacket size %0d", dut_rq.data.size())};
            err_msg = {err_msg, $sformatf("\n\t\tMaximum payload(%0d) exceeded %0d", MPS, dut_rq.data.size() > MPS)};
            err_msg = {err_msg, $sformatf("\n\t\tPage(%0d) boundary exceeded %0d addr 0x%h",
                                                    PAGE_SIZE,
                                                    tmp_addr > PAGE_SIZE,
                                                    {dut_rq.address, 2'b00})};
            `uvm_error(this.get_full_name(), err_msg);
        end

        // Delay statistic of the first data part of a packet (DMA data comparer only).
        if (ret != 0 && delay_stat != null && $cast(model_pkt, tr_model)
            && model_pkt.part == 1 && model_pkt.data_packet == 1) begin
            delay_stat.next_val((dut_rq.time_last() - model_pkt.time_last())/1ns);
        end

        return ret;
    endfunction
endclass


class scoreboard #(
    int unsigned USR_MFB_ITEM_WIDTH,
    int unsigned CHANNELS,
    int unsigned PKT_SIZE_MAX,
    string DEVICE,
    int unsigned POINTER_WIDTH,
    int unsigned SW_ADDR_WIDTH
) extends uvm_scoreboard;

    `uvm_component_param_utils(uvm_dma_ll::scoreboard #(USR_MFB_ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX, DEVICE,
                                                        POINTER_WIDTH, SW_ADDR_WIDTH))

    localparam LOGIC_WIDTH            = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);
    localparam IS_INTEL_DEV           = (DEVICE == "STRATIX10" || DEVICE == "AGILEX");
    localparam PTR_UPD_REQ_MVB_ITEM_W = 2*POINTER_WIDTH + 1 + SW_ADDR_WIDTH;

    //INPUT TO DUT
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(USR_MFB_ITEM_WIDTH)) m_usr_mfb_data_exp;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(LOGIC_WIDTH))              m_usr_mfb_meta_exp;

    //DUT OUTPUT
    uvm_analysis_export #(uvm_pcie::header)              m_pcie_rq_data_dut;
    protected uvm_tlm_analysis_fifo #(uvm_pcie::header)  m_pcie_rq_data_dut_meter;

    uvm_analysis_export #(uvm_logic_vector::sequence_item #(PTR_UPD_REQ_MVB_ITEM_W)) m_ptr_upd_req_mvb_exp;

    uvm_analysis_export #(uvm_pcie::header)              m_pcie_rq_upd_dut;

    // Models with comparers of their output against the DUT output
    local dma_model #(USR_MFB_ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX) m_dma_model;
    local ptr_updater_model #(POINTER_WIDTH, SW_ADDR_WIDTH)       m_ptr_updater_model;
    local pcie_rq_comparer #(dma_model_packet)                    m_data_cmp;
    local pcie_rq_comparer #(uvm_pcie::request_header)            m_upd_cmp;

    local uvm_common::stats                                                                    m_input_speed_stat;
    local uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(USR_MFB_ITEM_WIDTH)) m_input_speed_meter_fifo;
    local uvm_common::stats                                                                    m_delay_stat;
    local uvm_common::stats                                                                    m_output_speed_stat;

    local int unsigned m_dma_tr_compared     = 0;
    local int unsigned m_dma_tr_errors       = 0;
    local int unsigned m_ptr_upd_tr_compared = 0;
    local int unsigned m_ptr_upd_tr_errors   = 0;

    uvm_reg_data_t m_pkt_cnt          [CHANNELS];
    uvm_reg_data_t m_byte_cnt         [CHANNELS];
    uvm_reg_data_t m_discard_pkt_cnt  [CHANNELS];
    uvm_reg_data_t m_discard_byte_cnt [CHANNELS];

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        // DUT DMA_MODEL COMUNICATION
        m_usr_mfb_data_exp     = new("m_usr_mfb_data_exp", this);
        m_usr_mfb_meta_exp     = new("m_usr_mfb_meta_exp", this);
        m_ptr_upd_req_mvb_exp  = new("m_ptr_upd_req_mvb_exp", this);
        m_pcie_rq_upd_dut      = new("m_pcie_rq_upd_dut", this);

        m_pcie_rq_data_dut        = new("m_pcie_rq_data_dut", this);
        m_pcie_rq_data_dut_meter  = new("m_pcie_rq_data_dut_meter", this);

        //LOCAL VARIABLES
        m_input_speed_stat       = new();
        m_input_speed_meter_fifo = new("m_input_speed_meter_fifo", this);
        m_delay_stat             = new();
        m_output_speed_stat      = new();
    endfunction

    function void regmodel_set(regmodel #(CHANNELS) m_regmodel);
        m_dma_model.regmodel_set(m_regmodel);
    endfunction

    //build phase
    function void build_phase(uvm_phase phase);
        m_dma_model         = dma_model #(USR_MFB_ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX)::type_id
                              ::create("m_dma_model", this);
        m_ptr_updater_model = ptr_updater_model #(POINTER_WIDTH, SW_ADDR_WIDTH)::type_id
                              ::create("m_ptr_updater_model", this);

        m_data_cmp = pcie_rq_comparer #(dma_model_packet)::type_id::create("m_data_cmp", this);
        m_data_cmp.delay_stat = m_delay_stat;
        m_upd_cmp  = pcie_rq_comparer #(uvm_pcie::request_header)::type_id::create("m_upd_cmp", this);
        // The model expectations are synchronized to the DUT header-manager probe,
        // which triggers when the DUT emits the packet DMA header (the last
        // transaction of the packet). The DUT therefore legitimately leads the
        // model by the packet emission time, so the DUT-side delay watchdog must
        // stay effectively disabled; unpaired transactions are reported by
        // check_phase instead.
        m_data_cmp.model_tr_timeout_set(10s);
        m_upd_cmp.model_tr_timeout_set(10s);
    endfunction

    function void connect_phase(uvm_phase phase);
        m_usr_mfb_data_exp.connect(m_dma_model.m_usr_mfb_data_fifo.analysis_export);
        m_usr_mfb_meta_exp.connect(m_dma_model.m_usr_mfb_meta_fifo.analysis_export);
        m_dma_model.m_pcie_rq_mfb_port.connect(m_data_cmp.analysis_imp_model);

        m_pcie_rq_upd_dut.connect(m_upd_cmp.analysis_imp_dut);

        m_ptr_upd_req_mvb_exp.connect(m_ptr_updater_model.m_ptr_upd_req_fifo.analysis_export);
        m_ptr_updater_model.m_ptr_upd_rq_mfb_port.connect(m_upd_cmp.analysis_imp_model);

        m_usr_mfb_data_exp.connect(m_input_speed_meter_fifo.analysis_export);

        m_pcie_rq_data_dut.connect(m_pcie_rq_data_dut_meter.analysis_export);
        m_pcie_rq_data_dut.connect(m_data_cmp.analysis_imp_dut);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_data_cmp.used() != 0);
        ret |= (m_upd_cmp.used() != 0);
        ret |= (m_dma_model.used() != 0);
        ret |= (m_ptr_updater_model.used() != 0);
        return ret;
    endfunction

    task run_input_meter();
        int unsigned speed_packet_size = 0;
        time         speed_start_time  = 0ns;

        forever begin
            uvm_logic_vector_array::sequence_item #(USR_MFB_ITEM_WIDTH) tr;
            time                                                        time_act;
            time                                                        speed_metet_duration;

            m_input_speed_meter_fifo.get(tr);
            time_act = $time();

            speed_packet_size += tr.data.size();
            speed_metet_duration = time_act - speed_start_time;
            if (speed_metet_duration >= 10us) begin
                real speed;
                speed =  real'(speed_packet_size) / (speed_metet_duration/1ns); //result is in GB/s
                m_input_speed_stat.next_val(speed);
                speed_start_time  = time_act;
                speed_packet_size = 0;
            end
        end
    endtask

    task run_data_meter();
        int unsigned speed_packet_size = 0;
        time         speed_start_time  = 0ns;

        forever begin
            time time_act;
            time speed_metet_duration;
            uvm_pcie::header dut_hdr;

            m_pcie_rq_data_dut_meter.get(dut_hdr);

            //////////////////////////////
            // SPEED MESURMENT
            time_act = $time();
            speed_packet_size += dut_hdr.data.size();
            speed_metet_duration = time_act - speed_start_time;
            if (speed_metet_duration >= 10us) begin
                real speed;
                speed =  real'(speed_packet_size) / (speed_metet_duration/1ns); //result is in GB/s
                m_output_speed_stat.next_val(speed);
                speed_start_time  = time_act;
                speed_packet_size = 0;
            end
        end
    endtask

    task run_phase(uvm_phase phase);

        // Two routines that insert times for input and output transactions for throughput and latency measurement
        fork
            run_data_meter();
            run_input_meter();
        join
    endtask

    function void report_phase(uvm_phase phase);
        real   min;
        real   max;
        real   avg;
        real   std_dev;
        string str = "";
        int    pkt_cntr_diff;
        int    byte_cntr_diff;
        int    disc_pkt_cntr_diff;
        int    disc_byte_cntr_diff;

        // Take over the results of the comparers (their check_phase reports the
        // unpaired transactions).
        m_dma_tr_compared     = m_data_cmp.compared;
        m_dma_tr_errors       = m_data_cmp.errors;
        m_ptr_upd_tr_compared = m_upd_cmp.compared;
        m_ptr_upd_tr_errors   = m_upd_cmp.errors;

        //-----------------------------------------------------------------------
        // Counter statistics (latency and throughput on each interface)
        //-----------------------------------------------------------------------
        str = {str, $sformatf("\n\t------------------------------------------------------------------\n")};
        str = {str, $sformatf("\tPacket counters\n")};
        str = {str, $sformatf("\t------------------------------------------------------------------\n")};

        str = {str, $sformatf("\t------------------------------------------------------------------------\n")};
        str = {str, $sformatf("\t|          |                           Packets                         |\n")};
        str = {str, $sformatf("\t|          |-----------------------------------------------------------|\n")};
        str = {str, $sformatf("\t|  Channel |          Received           |          Discarded          |\n")};
        str = {str, $sformatf("\t|          |-----------------------------|-----------------------------|\n")};
        str = {str, $sformatf("\t|          |  Model  |   DUT   |   Diff  |  Model  |   DUT   |   Diff  |\n")};
        str = {str, $sformatf("\t|-----------------------------------------------------------------------\n")};

        for (int unsigned it = 0; it < CHANNELS; it++) begin
            pkt_cntr_diff       = m_pkt_cnt[it]          - m_dma_model.m_pkt_cntrs_storage.pkt_sent_cntr[it];
            disc_pkt_cntr_diff  = m_discard_pkt_cnt[it]  - m_dma_model.m_pkt_cntrs_storage.pkt_disc_cntr[it];

            str = {str, $sformatf("\t|   %2d     |  %6d |  %6d |  %6d |  %6d |  %6d |  %6d |\n",
                                  it,
                                  m_dma_model.m_pkt_cntrs_storage.pkt_sent_cntr[it],
                                  m_pkt_cnt[it],
                                  pkt_cntr_diff,
                                  m_dma_model.m_pkt_cntrs_storage.pkt_disc_cntr[it],
                                  m_discard_pkt_cnt[it],
                                  disc_pkt_cntr_diff
                                  )};

            if (pkt_cntr_diff != 0 || disc_pkt_cntr_diff != 0) begin
                m_dma_tr_errors++;
            end
        end

        str = {str, $sformatf("\t--------------------------------------------------------------------------------\n")};
        str = {str, $sformatf("\t|      |                                 Bytes                                 |\n")};
        str = {str, $sformatf("\t|      |-----------------------------------------------------------------------|\n")};
        str = {str, $sformatf("\t| Chan |              Received             |             Discarded             |\n")};
        str = {str, $sformatf("\t|      |-----------------------------------|-----------------------------------|\n")};
        str = {str, $sformatf("\t|      |   Model   |    DUT    |    Diff   |   Model   |    DUT    |    Diff   |\n")};
        str = {str, $sformatf("\t|------------------------------------------------------------------------------|\n")};

        for (int unsigned it = 0; it < CHANNELS; it++) begin
            byte_cntr_diff      = m_byte_cnt[it]         - m_dma_model.m_pkt_cntrs_storage.bytes_sent_cntr[it];
            disc_byte_cntr_diff = m_discard_byte_cnt[it] - m_dma_model.m_pkt_cntrs_storage.bytes_disc_cntr[it];

            str = {str, $sformatf("\t|  %2d  |  %8d |  %8d |  %8d |  %8d |  %8d |  %8d |\n",
                                  it,
                                  m_dma_model.m_pkt_cntrs_storage.bytes_sent_cntr[it],
                                  m_byte_cnt[it],
                                  byte_cntr_diff,
                                  m_dma_model.m_pkt_cntrs_storage.bytes_disc_cntr[it],
                                  m_discard_byte_cnt[it],
                                  disc_byte_cntr_diff
                                  )};

            if (byte_cntr_diff != 0 || disc_byte_cntr_diff != 0) begin
                m_dma_tr_errors++;
            end
        end
        //-----------------------------------------------------------------------
        // Performance statistics (latency and throughput on each interface)
        //-----------------------------------------------------------------------
        str = {str, $sformatf("\n\t------------------------------------------------------------------\n")};
        str = {str, $sformatf("\tPerformance statistics\n")};
        str = {str, $sformatf("\t------------------------------------------------------------------\n")};
        m_delay_stat.count(min, max, avg, std_dev);
        str = {str, $sformatf({"\tDelay statistic (SOF to SOF) => min : %0dns, max : %0dns, avearge : %0dns, ",
                               "standard deviation : %0dns\n"},  min, max, avg, std_dev)};
        m_input_speed_stat.count(min, max, avg, std_dev);
        str = {str, $sformatf({"\tSpeed input  statistic (MFB RX)  => min : %0dGb/s, max : %0dGb/s, avearge : %0dG/s, ",
                               "standard deviation : %0dG/s\n"},  min*8, max*8, avg*8, std_dev*8)};
        m_output_speed_stat.count(min, max, avg, std_dev);
        str = {str, $sformatf({"\tSpeed output statistic (PCIE TX) => min : %0dGb/s, max : %0dGb/s, avearge : %0dG/s, ",
                              "standard deviation : %0dG/s\n"},  min*8, max*8, avg*8, std_dev*8)};

        if (m_dma_tr_errors == 0 && m_ptr_upd_tr_errors == 0) begin
            `uvm_info(this.get_full_name(), {str, "\n\n\t---------------------------------------",
                                                  "\n\t----     VERIFICATION SUCCESS      ----",
                                                  "\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(this.get_full_name(), {str, "\n\n\t---------------------------------------",
                                                  "\n\t----     VERIFICATION FAIL      ----",
                                                  "\n\t---------------------------------------"}, UVM_NONE)
        end
    endfunction
endclass
