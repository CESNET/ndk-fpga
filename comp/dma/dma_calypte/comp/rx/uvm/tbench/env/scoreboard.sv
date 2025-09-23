//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX, META_WIDTH, DEVICE) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_dma_ll::scoreboard #(ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX, META_WIDTH, DEVICE))

    localparam LOGIC_WIDTH  = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);
    localparam IS_INTEL_DEV = (DEVICE == "STRATIX10" || DEVICE == "AGILEX");
    localparam MPS          = 256;
    localparam PAGE_SIZE    = 4096;

    //INPUT TO DUT
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)) m_usr_mfb_data_exp;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(LOGIC_WIDTH))      m_usr_mfb_meta_exp;

    //DUT WATCH INTERFACE
    uvm_analysis_export #(uvm_mvb::sequence_item #(1, 1)) m_pkt_disc_mvb_exp;

    //DUT OUTPUT
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(32))           m_pcie_rq_mfb_data_exp;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(META_WIDTH))         m_pcie_rq_mfb_meta_exp;

    //OUTPUT TO model
    local uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(32))         m_pcie_rq_mfb_data_fifo;
    local uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(META_WIDTH))       m_pcie_rq_mfb_meta_fifo;
    local uvm_tlm_analysis_fifo #(model_packet)                                        m_model_output_fifo;
    local model #(ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX)                                  m_model;
    local regmodel #(CHANNELS)                                                         m_regmodel;
    local uvm_common::stats                                                            m_input_speed_stat;
    local uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)) m_input_speed_meter_fifo;
    local uvm_common::stats                                                            m_delay_stat;
    local uvm_common::stats                                                            m_output_speed_stat;

    local int unsigned m_compared = 0;
    local int unsigned m_errors   = 0;

    typedef struct{
        uvm_logic_vector_array::sequence_item #(32)   item;
        uvm_logic_vector::sequence_item #(META_WIDTH) meta;
        time output_time;
    } output_type;

    local output_type m_out_data[$];

    uvm_reg_data_t m_pkt_cnt          [CHANNELS];
    uvm_reg_data_t m_byte_cnt         [CHANNELS];
    uvm_reg_data_t m_discard_pkt_cnt  [CHANNELS];
    uvm_reg_data_t m_discard_byte_cnt [CHANNELS];

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        // DUT MODEL COMUNICATION
        m_usr_mfb_data_exp     = new("m_usr_mfb_data_exp", this);
        m_usr_mfb_meta_exp     = new("m_usr_mfb_meta_exp", this);
        m_pkt_disc_mvb_exp     = new("m_pkt_disc_mvb_exp", this);
        m_pcie_rq_mfb_data_exp = new("m_pcie_rq_mfb_data_exp", this);
        m_pcie_rq_mfb_meta_exp = new("m_pcie_rq_mfb_meta_exp", this);

        m_model_output_fifo     = new("m_model_output_fifo", this);
        m_pcie_rq_mfb_data_fifo = new("m_pcie_rq_mfb_data_fifo", this);
        m_pcie_rq_mfb_meta_fifo = new("m_pcie_rq_mfb_meta_fifo", this);

        //LOCAL VARIABLES
        m_input_speed_meter_fifo = new("m_input_speed_meter_fifo", this);
        m_delay_stat             = new();
        m_output_speed_stat      = new();
        m_input_speed_stat       = new();
    endfunction

    function void regmodel_set(regmodel#(CHANNELS) m_regmodel);
        this.m_regmodel = m_regmodel;
        m_model.regmodel_set(m_regmodel);
    endfunction

    //build phase
    function void build_phase(uvm_phase phase);
        m_model = model #(ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX)::type_id::create("m_model", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        m_usr_mfb_data_exp.connect(m_model.m_usr_mfb_data_fifo.analysis_export);
        m_usr_mfb_data_exp.connect(m_input_speed_meter_fifo.analysis_export);
        m_usr_mfb_meta_exp.connect(m_model.m_usr_mfb_meta_fifo.analysis_export);
        m_pkt_disc_mvb_exp.connect(m_model.m_pkt_disc_mvb_subs.analysis_export);
        m_pcie_rq_mfb_data_exp.connect(m_pcie_rq_mfb_data_fifo.analysis_export);
        m_pcie_rq_mfb_meta_exp.connect(m_pcie_rq_mfb_meta_fifo.analysis_export);
        m_model.m_pcie_rq_mfb_port.connect(m_model_output_fifo.analysis_export);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_pcie_rq_mfb_data_fifo.used() != 0);
        ret |= (m_pcie_rq_mfb_meta_fifo.used() != 0);
        ret |= (m_model_output_fifo.used() != 0);
        ret |= (m_model.used() != 0);
        return ret;
    endfunction

    function bit pcie_compare(
                              uvm_logic_vector_array::sequence_item#(32) tr_dut,
                              uvm_logic_vector::sequence_item#(META_WIDTH) tr_meta_dut,
                              model_packet tr_model);
        bit ret = 1;

        logic [3-1:0]   fmt;
        logic [5-1:0]   pcie_type;

        logic [2-1:0]   at;
        logic [3-1:0]   attr;
        logic [3-1:0]   tc;
        logic [8-1:0]   tag;
        logic [16-1:0]  requester_id;
        logic [1-1:0]   ep;
        logic [1-1:0]   th = 0;
        logic [4-1 : 0] fbe;
        logic [4-1 : 0] lbe;
        logic [10-1:0]  length; //size in dwords
        logic [32-1:0]  data[];
        logic [64-1:2]  addr;
        logic [2-1:0]   ph;
        logic [1-1:0]   td;
        int unsigned    min_length;

        if (IS_INTEL_DEV) begin // Intel P/R-Tile
            logic [1-1:0] tag_8;
            logic [1-1:0] tag_9;
            logic [1-1:0] ln = 0;

            // This is strench
            {fmt, pcie_type, tag_9, tc, tag_8, attr[2], ln, th, td, ep, attr[2-1:0], at, length} = tr_meta_dut.data[32-1 -: 32];
            if (fmt[0] == 1'b0) begin
                addr[64-1:32] = 0;
                {requester_id, tag, lbe, fbe, addr[32-1:2], ph} = {tr_meta_dut.data[64-1 -: 32], tr_meta_dut.data[96-1 -: 32]};
            end else begin
                {requester_id, tag, lbe, fbe, addr, ph} = {tr_meta_dut.data[64-1 -: 32], tr_meta_dut.data[96-1 -: 32], tr_meta_dut.data[128-1 -: 32]};
            end

            if ({fmt, pcie_type} != 8'b01100000 && {fmt, pcie_type} != 8'b01000000) begin
                `uvm_error(this.get_full_name(), $sformatf("\nUnsupporte request\n\tfmt : 0x%h\n\ttype : 0x%h\n", fmt, pcie_type));
            end


            data = tr_dut.data;

            ret &= ln === 0;
            ret &= tag_8 === 0;
            ret &= tag_9 === 0;
            ret &= tr_meta_dut.data[160-1 : 128] === 0;

        end else begin // Xilinx FPGA
            logic [16-1:0] cm_id; //compleater ID
            logic [1-1:0]  ecrc;
            logic [1-1:0]  rq_id_enabled;
            logic [11-1:0] dword_count; //size in dwords
            logic [4-1:0]  rq_type;
            logic [32-1:0] hdr[4];

            {ecrc, attr, tc, rq_id_enabled, cm_id, tag, requester_id, ep, rq_type, dword_count, addr[64-1:2], at} = {tr_dut.data[3], tr_dut.data[2], tr_dut.data[1], tr_dut.data[0]};
            data = new[tr_dut.data.size() -4];
            for (int unsigned it = 0; it < tr_dut.data.size() -4; it++) begin
                data[it] = tr_dut.data[it+4];
            end

            td = 0;
            fbe = tr_meta_dut.data[164-1 : 160];
            lbe = tr_meta_dut.data[168-1 : 164];
            ph   = 0;

            ret &=  ecrc === 0;
            ret &=  rq_type === 4'h1;
            fmt       = addr[64-1:32] != 0 ? 3'b011 : 3'b011;
            pcie_type = 5'b00000;
            ret &= dword_count !== 0 && dword_count <= 1024;
            length = dword_count;
            ret &= rq_id_enabled === 0;
            ret &= cm_id === 0;
        end

        ret &= (fmt            ==? tr_model.fmt      ) === 1'b1;
        ret &= (pcie_type      ==? tr_model.pcie_type) === 1'b1;
        ret &= (at             ==? tr_model.at) === 1'b1;
        ret &= (attr[2]        ==? tr_model.id_based_ordering) === 1'b1;
        ret &= (attr[1]        ==? tr_model.relaxed_ordering ) === 1'b1;
        ret &= (attr[0]        ==? tr_model.no_snoop         ) === 1'b1;
        ret &= (tc             ==? tr_model.traffic_class) === 1'b1;
        ret &= (tag            ==? tr_model.tag) === 1'b1;
        ret &= (requester_id   ==? tr_model.requester_id) === 1'b1;
        ret &= (ep             ==? tr_model.ep) === 1'b1;
        ret &= (th             ==? tr_model.th) === 1'b1;
        ret &= (td             ==? tr_model.td) === 1'b1;
        ret &= (fbe            ==? tr_model.fbe) === 1'b1;
        ret &= (lbe            ==? tr_model.lbe) === 1'b1;
        ret &= (addr           ==? tr_model.address) === 1'b1;
        ret &= (length         ==? tr_model.length) === 1'b1;
        ret &= (ph             ==? tr_model.ph) === 1'b1;

        min_length= ((tr_dut.data.size()-4) < tr_model.data.size()) ? tr_dut.data.size()-4 : tr_model.data.size();

        if ((length == tr_model.length) && (tr_dut.data.size()-4 == tr_model.data.size())) begin
            for (int j = 0; j < 4; j++) begin
                if (fbe[j] === 1'b1) begin
                    ret &= (data[0][8*j +: 8] ==? tr_model.data[0][8*j +: 8]) === 1'b1;
                end
            end

            for (int unsigned it = 1; it < length-1; it++) begin
                ret &= (data[it] ==? tr_model.data[it]) === 1'b1;
            end

            for (int j = 0; j < 4; j++) begin
                if (lbe[j] === 1'b1) begin
                    ret &= (data[length-1][8*j +: 8] ==? tr_model.data[length-1][8*j +: 8]) === 1'b1;
                end
            end

            //Check pcie requiretments
            if (data.size() > MPS || (((addr & (PAGE_SIZE-1)) + data.size()) > PAGE_SIZE)) begin
                `uvm_error(this.get_full_name(), $sformatf("\n\tPacket doesn't meet pcie requirements.\n\t\tPacket size %0d\n\t\tMaximum payload(%0d) exceeded %0d\n\t\tPage(%0d) boundary exceeded %0d addr 0x%h",
                                        data.size(), MPS, data.size() > MPS, PAGE_SIZE, (((addr & (PAGE_SIZE-1)) + data.size()) > PAGE_SIZE), addr));
            end
        end

        return ret;
    endfunction

    task run_input();
        int unsigned speed_packet_size = 0;
        time         speed_start_time  = 0ns;

        forever begin
            uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) tr;
            time                                               time_act;
            time                                               speed_metet_duration;

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

    task run_output();
        uvm_logic_vector_array::sequence_item #(32)   tr_dut;
        uvm_logic_vector::sequence_item #(META_WIDTH) tr_meta;
        output_type                                   data;
        int unsigned                                  speed_packet_size = 0;
        time                                          speed_start_time  = 0ns;

        forever begin
            time time_act;
            time speed_metet_duration;

            m_pcie_rq_mfb_meta_fifo.get(tr_meta);
            data.meta = tr_meta;

            m_pcie_rq_mfb_data_fifo.get(tr_dut);
            time_act = $time();

            data.item        = tr_dut;
            data.output_time = time_act;
            m_out_data.push_back(data);

            speed_packet_size += tr_dut.data.size();
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
        string        msg = "";
        model_packet  packet_model;
        output_type   tr_dut;

        fork
            run_output();
            run_input();
        join_none

        forever begin
            msg = "";

            wait (m_out_data.size() != 0);
            tr_dut = m_out_data.pop_front();

            m_model_output_fifo.get(packet_model);

            m_compared++;
            msg = $sformatf("\nSegments compared : %0d, segments erroneous: %0d. Channel: %0d, Packet num %0d", m_compared, m_errors, packet_model.channel, packet_model.packet_num);

            if (pcie_compare(tr_dut.item, tr_dut.meta, packet_model) == 0) begin
                m_errors++;

                msg = {msg, $sformatf("\nExpected transaction is:\n\t\tPart is : %s\n\t\tChannel : %0d\n\t\tPart %0d/%0d\n\t\tInput time %d\n\t\t\t",  packet_model.data_packet == 1 ? "DATA" : "HEADER",  packet_model.channel, packet_model.part, packet_model.part_num, packet_model.time2string())};
                msg = {msg, $sformatf("\n\tDUT Transaction doesnt match Model transaction\n\tDUT Transaction : \n\tMETA : %s\n\tDATA : %s\nMODEL TRANSACTION %s\n", tr_dut.meta.convert2string(), tr_dut.item.convert2string(), packet_model.convert2string())};
                `uvm_error(this.get_full_name(), msg);
            end else begin
                msg = {msg, $sformatf("\nRecive correct transaction :\n\t\tSegment contains: %s\n\t\tChannel : %0d\n\t\tPart %0d/%0d\n\t\tPart is delay from SOF on input %0dns",  packet_model.data_packet == 1 ? "DATA" : "HEADER",  packet_model.channel, packet_model.part, packet_model.part_num, (tr_dut.output_time - packet_model.time_last())/1ns)};
                `uvm_info(this.get_full_name(), $sformatf("%s\nTransaction%s", msg, packet_model.convert2string()), UVM_MEDIUM);
            end

            //Count delay if you get first data packet.
            if (packet_model.part == 1 && packet_model.data_packet == 1) begin
                m_delay_stat.next_val((tr_dut.output_time - packet_model.time_last())/1ns);
            end
        end
    endtask

    function void check_phase(uvm_phase phase);

        if (m_pcie_rq_mfb_data_fifo.size() != 0 || m_pcie_rq_mfb_meta_fifo.size() != 0 || m_model_output_fifo.size() != 0) begin
            `uvm_error(this.get_full_name(), $sformatf("\nExpected some data\n\tMODELs transactions (%0d)\n\tDUTs data packets(%0d) meta(%0d)", m_model_output_fifo.size(), m_pcie_rq_mfb_data_fifo.size(), m_pcie_rq_mfb_meta_fifo.size()));
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

        str = {str, $sformatf("\t------------------------------------------------------------------------------------------------------------------------------------------------\n")};
        str = {str, $sformatf("\t|          |                           Packets                         |                                 Bytes                                 |\n")};
        str = {str, $sformatf("\t|          |-----------------------------------------------------------|-----------------------------------------------------------------------|\n")};
        str = {str, $sformatf("\t|  Channel |          Received           |          Discarded          |              Received             |             Discarded             |\n")};
        str = {str, $sformatf("\t|          |-----------------------------|-----------------------------|-----------------------------------|-----------------------------------|\n")};
        str = {str, $sformatf("\t|          |  Model  |   DUT   |   Diff  |  Model  |   DUT   |   Diff  |   Model   |    DUT    |    Diff   |   Model   |    DUT    |    Diff   |\n")};
        str = {str, $sformatf("\t|----------------------------------------------------------------------------------------------------------------------------------------------|\n")};

        for (int unsigned it = 0; it < CHANNELS; it++) begin
            pkt_cntr_diff       = m_pkt_cnt[it]          - m_model.m_pkt_cntrs_storage.pkt_sent_cntr[it];
            byte_cntr_diff      = m_byte_cnt[it]         - m_model.m_pkt_cntrs_storage.bytes_sent_cntr[it];
            disc_pkt_cntr_diff  = m_discard_pkt_cnt[it]  - m_model.m_pkt_cntrs_storage.pkt_disc_cntr[it];
            disc_byte_cntr_diff = m_discard_byte_cnt[it] - m_model.m_pkt_cntrs_storage.bytes_disc_cntr[it];

            str = {str, $sformatf("\t|   %2d     |  %6d |  %6d |  %6d |  %6d |  %6d |  %6d |  %8d |  %8d |  %8d |  %8d |  %8d |  %8d |\n",
                                  it,
                                  m_model.m_pkt_cntrs_storage.pkt_sent_cntr[it],
                                  m_pkt_cnt[it],
                                  pkt_cntr_diff,
                                  m_model.m_pkt_cntrs_storage.pkt_disc_cntr[it],
                                  m_discard_pkt_cnt[it],
                                  disc_pkt_cntr_diff,
                                  m_model.m_pkt_cntrs_storage.bytes_sent_cntr[it],
                                  m_byte_cnt[it],
                                  byte_cntr_diff,
                                  m_model.m_pkt_cntrs_storage.bytes_disc_cntr[it],
                                  m_discard_byte_cnt[it],
                                  disc_byte_cntr_diff
                                  )};

            if (pkt_cntr_diff != 0 || byte_cntr_diff != 0 || disc_pkt_cntr_diff != 0 || disc_byte_cntr_diff != 0)
                m_errors++;
        end

        //-----------------------------------------------------------------------
        // Performance statistics (latency and throughput on each interface)
        //-----------------------------------------------------------------------
        str = {str, $sformatf("\n\t------------------------------------------------------------------\n")};
        str = {str, $sformatf("\tPerformance statistics\n")};
        str = {str, $sformatf("\t------------------------------------------------------------------\n")};
        m_delay_stat.count(min, max, avg, std_dev);
        str = {str, $sformatf("\tDelay statistic (SOF to SOF) => min : %0dns, max : %0dns, avearge : %0dns, standard deviation : %0dns\n",  min, max, avg, std_dev)};
        m_input_speed_stat.count(min, max, avg, std_dev);
        str = {str, $sformatf("\tSpeed input  statistic (MFB RX)  => min : %0dGb/s, max : %0dGb/s, avearge : %0dG/s, standard deviation : %0dG/s\n",  min*8, max*8, avg*8, std_dev*8)};
        m_output_speed_stat.count(min, max, avg, std_dev);
        str = {str, $sformatf("\tSpeed output statistic (PCIE TX) => min : %0dGb/s, max : %0dGb/s, avearge : %0dG/s, standard deviation : %0dG/s\n",  min*8, max*8, avg*8, std_dev*8)};

        if (m_errors == 0) begin
            `uvm_info(this.get_full_name(), {str, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(this.get_full_name(), {str, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------"}, UVM_NONE)
        end
    endfunction
endclass
