//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

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
    localparam MPS                    = 256;
    localparam PAGE_SIZE              = 4096;
    localparam PTR_UPD_REQ_MVB_ITEM_W = 2*POINTER_WIDTH + 1 + SW_ADDR_WIDTH;

    //INPUT TO DUT
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(USR_MFB_ITEM_WIDTH)) m_usr_mfb_data_exp;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(LOGIC_WIDTH))              m_usr_mfb_meta_exp;

    //DUT OUTPUT
    uvm_analysis_export #(uvm_pcie::header)              m_pcie_rq_data_dut;
    protected uvm_tlm_analysis_fifo #(uvm_pcie::header)  m_pcie_rq_data_dut_meter;
    protected uvm_tlm_analysis_fifo #(uvm_pcie::header)  m_pcie_rq_data_dut_cmp;

    uvm_analysis_export #(uvm_logic_vector::sequence_item #(PTR_UPD_REQ_MVB_ITEM_W)) m_ptr_upd_req_mvb_exp;

    uvm_analysis_export #(uvm_pcie::header)              m_pcie_rq_upd_dut;
    protected uvm_tlm_analysis_fifo #(uvm_pcie::header)  m_pcie_rq_upd_dut_cmp;

    // Models with their output fifos
    local dma_model #(USR_MFB_ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX) m_dma_model;
    local uvm_tlm_analysis_fifo #(dma_model_packet)               m_dma_model_output_fifo;
    local ptr_updater_model #(POINTER_WIDTH, SW_ADDR_WIDTH)       m_ptr_updater_model;
    local uvm_tlm_analysis_fifo #(uvm_pcie::request_header)       m_ptr_upd_model_output_fifo;

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
        m_pcie_rq_upd_dut       = new("m_pcie_rq_upd_dut", this);
        m_pcie_rq_upd_dut_cmp   = new("m_pcie_rq_upd_dut_cmp", this);

        m_pcie_rq_data_dut = new("m_pcie_rq_data_dut", this);
        m_pcie_rq_data_dut_meter  = new("m_pcie_rq_data_dut_meter", this);
        m_pcie_rq_data_dut_cmp    = new("m_pcie_rq_data_dut_cmp", this);
        m_dma_model_output_fifo     = new("m_dma_model_output_fifo", this);
        m_ptr_upd_model_output_fifo = new("m_ptr_upd_model_output_fifo", this);

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
    endfunction

    function void connect_phase(uvm_phase phase);
        m_usr_mfb_data_exp.connect(m_dma_model.m_usr_mfb_data_fifo.analysis_export);
        m_usr_mfb_meta_exp.connect(m_dma_model.m_usr_mfb_meta_fifo.analysis_export);
        m_dma_model.m_pcie_rq_mfb_port.connect(m_dma_model_output_fifo.analysis_export);

        m_pcie_rq_upd_dut.connect(m_pcie_rq_upd_dut_cmp  .analysis_export);

        m_ptr_upd_req_mvb_exp.connect(m_ptr_updater_model.m_ptr_upd_req_fifo.analysis_export);
        m_ptr_updater_model.m_ptr_upd_rq_mfb_port.connect(m_ptr_upd_model_output_fifo.analysis_export);

        m_usr_mfb_data_exp.connect(m_input_speed_meter_fifo.analysis_export);

        m_pcie_rq_data_dut.connect(m_pcie_rq_data_dut_meter.analysis_export);
        m_pcie_rq_data_dut.connect(m_pcie_rq_data_dut_cmp  .analysis_export);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_pcie_rq_data_dut_cmp.used() != 0);
        ret |= (m_dma_model_output_fifo.used() != 0);
        ret |= (m_ptr_upd_model_output_fifo.used() != 0);
        ret |= (m_dma_model.used() != 0);
        ret |= (m_ptr_updater_model.used() != 0);
        ret |= (m_pcie_rq_upd_dut_cmp.used() != 0);
        return ret;
    endfunction

    function bit pcie_compare(
            uvm_pcie::request_header  dut,
            uvm_pcie::request_header  model
        );

        bit ret = 1;

        ret &= dut.fmt                === model.fmt;
        ret &= dut.pcie_type          === model.pcie_type;
        ret &= dut.traffic_class      === model.traffic_class;
        ret &= dut.id_based_ordering  === model.id_based_ordering;
        ret &= dut.relaxed_ordering   === model.relaxed_ordering;
        ret &= dut.no_snoop           === model.no_snoop;
        ret &= dut.th                 === model.th; // TLP Processing Hints
        ret &= dut.td                 === model.td;
        ret &= dut.ep                 === model.ep; // poisoned
        ret &= dut.at                 === model.at;
        ret &= dut.length             === model.length; //dwords
        ret &= (dut.data              ==? model.data) === 1'b1;
        ret &= dut.requester_id       === model.requester_id;
        ret &= dut.tag                === model.tag;
        ret &= dut.lbe                === model.lbe;
        ret &= dut.fbe                === model.fbe;
        ret &= dut.address            === model.address;
        ret &= dut.ph                 === model.ph;

        //Check pcie requiretments
        if (dut.data.size() > MPS || ((({dut.address, 2'b00} & (PAGE_SIZE-1)) + dut.data.size()) > PAGE_SIZE)) begin
            string err_msg = $sformatf("\n\tPacket doesn't meet pcie requirements.");
            err_msg = {err_msg, $sformaf("\n\t\tPacket size %0d", dut.data.size())};
            err_msg = {err_msg, $sformaf("\n\t\tMaximum payload(%0d) exceeded %0d", MPS, dut.data.size() > MPS)};
            err_msg = {err_msg, $sformaf("\n\t\tPage(%0d) boundary exceeded %0d addr 0x%h", PAGE_SIZE,
                                         ((({dut.address, 2'b00} & (PAGE_SIZE-1)) + dut.data.size()) > PAGE_SIZE), {dut.address, 2'b00})};
            `uvm_error(this.get_full_name(), err_msg);
        end

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

    task run_data_cmp();
        forever begin
            string msg;
            uvm_pcie::request_header  dut_hdr_rq;
            uvm_pcie::header dut_hdr;
            dma_model_packet model_hdr;

            m_pcie_rq_data_dut_cmp.get(dut_hdr);
            assert($cast(dut_hdr_rq, dut_hdr));
            m_dma_model_output_fifo.get(model_hdr);

            m_dma_tr_compared++;

            msg = $sformatf("\nDMA Segments compared : %0d, segments erroneous: %0d. Channel: %0d, Packet num %0d",
                            m_dma_tr_compared, m_dma_tr_errors, model_hdr.channel,
                            model_hdr.packet_num);

            //if (tr_dut.compare(packet_dma_model) == 0) begin
            if (pcie_compare(dut_hdr_rq, model_hdr) == 0) begin
                m_dma_tr_errors++;

                msg = {msg, $sformatf("\nExpected transaction is:\n\t\tPart is : %s",
                                      model_hdr.data_packet == 1 ? "DATA" : "HEADER")};
                msg = {msg, $sformatf("\n\t\tChannel : %0d", model_hdr.channel)};
                msg = {msg, $sformatf("\n\t\tPart %0d/%0d", model_hdr.part, model_hdr.part_num)};
                msg = {msg, $sformatf("\n\t\tInput time\n\t\t\t%s", model_hdr.time2string())};
                msg = {msg, $sformatf("\n\tDUT Transaction doesnt match Model transaction")};
                msg = {msg, $sformatf("\n\tDUT Transaction: \n\t%s\n\t",
                                      dut_hdr.convert2string())};
                msg = {msg, $sformatf("\nMODEL TRANSACTION %s\n", model_hdr.convert2string())};
                `uvm_error(this.get_full_name(), msg);
            end else begin
                msg = {msg, $sformatf("\nRecive correct transaction:")};
                msg = {msg, $sformatf("\n\t\tSegment contains: %s", model_hdr.data_packet == 1
                                      ? "DATA" : "HEADER")};
                msg = {msg, $sformatf("\n\t\tChannel: %0d", model_hdr.channel)};
                msg = {msg, $sformatf("\n\t\tPart %0d/%0d", model_hdr.part, model_hdr.part_num)};
                msg = {msg, $sformatf("\n\t\tPart is delay from SOF on input %0dns",
                                      (dut_hdr.time_last() - model_hdr.time_last())/1ns)};
                `uvm_info(this.get_full_name(), $sformatf("%s\nTransaction%s", msg,
                                                          model_hdr.convert2string()), UVM_MEDIUM);

                //Count delay if you get first data packet.
                if (model_hdr.part == 1 && model_hdr.data_packet == 1) begin
                    m_delay_stat.next_val((dut_hdr.time_last() - model_hdr.time_last())/1ns);
                end
            end
        end
    endtask

    task run_upd_cmp();
        forever begin
            string msg;
            uvm_pcie::request_header model_tr;
            uvm_pcie::header dut_tr;
            uvm_pcie::request_header dut_rq_tr;


            m_pcie_rq_upd_dut_cmp.get(dut_tr);
            assert($cast(dut_rq_tr, dut_tr));
            m_ptr_upd_model_output_fifo.get(model_tr);

            m_ptr_upd_tr_compared++;
            msg = $sformatf("\nPTR_UPD tr compared : %0d, PTR_UPD tr erroneous: %0d.",
                            m_ptr_upd_tr_compared, m_ptr_upd_tr_errors);

            if (pcie_compare(dut_rq_tr, model_tr) == 0) begin
                m_ptr_upd_tr_errors++;

                msg = {msg, $sformatf("\nTransactions DO NOT match!")};
                msg = {msg, $sformatf("\n\t====== DUT ======t%s\n", dut_rq_tr.convert2string())};
                msg = {msg, $sformatf("\n\t====== MODEL ======\n\t%s\n", model_tr.convert2string())};
                `uvm_error(this.get_full_name(), msg);
            end else begin
                msg = {msg, $sformatf("\nReceived correct transaction: %s", model_tr.convert2string())};
                `uvm_info(this.get_full_name(), msg, UVM_MEDIUM);
            end
        end
    endtask

    task run_phase(uvm_phase phase);

        // Two routines that insert times for input and output transactions for throughput and latency measurement
        fork
            run_data_meter();
            run_data_cmp();
            run_input_meter();

            run_upd_cmp();
        join
    endtask

    function void check_phase(uvm_phase phase);
        string msg = "";

        if (m_pcie_rq_data_dut_cmp.used() != 0  || m_pcie_rq_upd_dut_cmp.size() != 0 || 
            m_dma_model_output_fifo.size() != 0 || m_ptr_upd_model_output_fifo.size() != 0) begin

            msg = {msg, "\nExpected some data\n:"};
            msg = {msg, $sformatf("\tDMA MODEL transactions: (%0d)\n", m_dma_model_output_fifo.size())};
            msg = {msg, $sformatf("\tDMA DUT data packets: (%0d)\n", m_pcie_rq_data_dut_cmp.size())};
            msg = {msg, $sformatf("\tPTR_UPDATER MODEL transactions: (%0d)\n", m_ptr_upd_model_output_fifo.size())};
            msg = {msg, $sformatf("\tPTR_UPDATER DUT data packets: (%0d)\n", m_pcie_rq_upd_dut_cmp.size())};
            `uvm_error(this.get_full_name(), msg);
        end
    endfunction

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
