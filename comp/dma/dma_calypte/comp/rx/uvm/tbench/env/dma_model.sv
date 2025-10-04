//-- dma_model.sv: Model of the DMA module
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class dma_model_packet extends uvm_pcie::request_header;
    `uvm_object_utils(uvm_dma_ll::dma_model_packet);

    bit          data_packet;
    int unsigned packet_num;
    int unsigned channel;
    int unsigned part;
    int unsigned part_num;

    function new(string name = "dma_model_packet");
        super.new(name);
        data_packet  = 0;
    endfunction
endclass


class dma_model_data;
    int unsigned data_ptr;
    int unsigned hdr_ptr;
    bit          vld_bit;
endclass


class status_cbs extends uvm_reg_cbs;
    dma_model_data data;

    function new(dma_model_data data);
        this.data = data;
    endfunction

    virtual task pre_write(uvm_reg_item rw);
        if(rw.value[0][0] == 1'b1) begin
            data.data_ptr = 0;
            data.hdr_ptr = 0;
            data.vld_bit = 1;
        end
    endtask
endclass

class dma_model_accept#(CHANNELS) extends uvm_subscriber#(uvm_mvb::sequence_item#(1, 1));
    `uvm_component_param_utils(uvm_dma_ll::dma_model_accept #(CHANNELS))
    logic fifo[$];

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        return fifo.size() != 0;
    endfunction

    virtual function void write(uvm_mvb::sequence_item#(1, 1) t);
        if (t.src_rdy == 1'b1 && t.dst_rdy == 1'b1) begin
            for (int unsigned it = 0; it < 1; it++) begin
                if (t.vld[it] == 1'b1) begin
                    fifo.push_back(t.data[it]);
                end
            end
        end
    endfunction
endclass

class disc_probe_cbs extends uvm_probe::cbs_simple #(1);
    `uvm_object_utils(uvm_dma_ll::disc_probe_cbs)

    function new(string name = "disc_probe_cbs");
        super.new(name);
    endfunction

    virtual function void post_trigger(uvm_event e, uvm_object data);
        super.post_trigger(e, data);
        `uvm_info(this.get_full_name(), $sformatf("\nDUT DROP: %0d %0dns\n", out[$], $time/1ns),  UVM_HIGH);
    endfunction
endclass

class dma_model #(ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX) extends uvm_component;
    `uvm_component_param_utils(uvm_dma_ll::dma_model #(ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX))

    localparam USER_META_WIDTH = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);

    localparam BLOCK_SIZE_BYTES = 128;
    localparam BLOCK_SIZE_DWS = BLOCK_SIZE_BYTES/4;

    //UVM PROBE - model input
    disc_probe_cbs m_probe_discard;

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)) m_usr_mfb_data_fifo;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(USER_META_WIDTH))  m_usr_mfb_meta_fifo;
    dma_model_accept #(CHANNELS)                                                 m_pkt_disc_mvb_subs;
    uvm_analysis_port #(dma_model_packet)                                        m_pcie_rq_mfb_port;

    typedef struct{
        logic [$clog2(PKT_SIZE_MAX+1)-1:0] packet_size;
        logic [$clog2(CHANNELS)-1:0]       channel;
        logic [24-1:0]                     meta;
        time                               input_time;
        logic [2-1:0]                      run; //[0] -> run, [1] -> soft compare
    } packet_info;

    local packet_info         m_input_meta[$];

    local regmodel#(CHANNELS) m_regmodel;
    local int unsigned        m_pkt_sent_cntr [CHANNELS];
    local int unsigned        m_pkt_disc_cntr [CHANNELS];
    local int unsigned        m_bytes_sent_cntr [CHANNELS];
    local int unsigned        m_bytes_disc_cntr [CHANNELS];
    local int unsigned        m_pkt_cntr_total_chan [CHANNELS];

    typedef struct {
        int unsigned pkt_sent_cntr [CHANNELS];
        int unsigned pkt_disc_cntr [CHANNELS];
        int unsigned bytes_sent_cntr [CHANNELS];
        int unsigned bytes_disc_cntr [CHANNELS];
    } pkt_cntrs_storage;

    pkt_cntrs_storage m_pkt_cntrs_storage;

    local dma_model_data m_data[CHANNELS];
    local status_cbs     m_status_cbs[CHANNELS];

    function new (string name, uvm_component parent = null);
        super.new(name, parent);
        m_usr_mfb_data_fifo = new("m_usr_mfb_data_fifo", this);
        m_usr_mfb_meta_fifo = new("m_usr_mfb_meta_fifo", this);
        m_pcie_rq_mfb_port  = new("m_pcie_rq_mfb_port", this);

        for (int unsigned it = 0; it < CHANNELS; it++) begin
            m_data[it]       = new();
            m_status_cbs[it] = new(m_data[it]);

            m_pkt_sent_cntr[it]                     = 0;
            m_pkt_disc_cntr[it]                     = 0;
            m_bytes_sent_cntr[it]                   = 0;
            m_bytes_disc_cntr[it]                   = 0;
            m_pkt_cntr_total_chan[it]               = 0;
            m_pkt_cntrs_storage.pkt_sent_cntr[it]   = 0;
            m_pkt_cntrs_storage.pkt_disc_cntr[it]   = 0;
            m_pkt_cntrs_storage.bytes_sent_cntr[it] = 0;
            m_pkt_cntrs_storage.bytes_disc_cntr[it] = 0;
        end
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_usr_mfb_data_fifo.used() != 0);
        ret |= (m_usr_mfb_meta_fifo.used() != 0);
        ret |= (m_pkt_disc_mvb_subs.used() != 0);
        return ret;
    endfunction

    function void regmodel_set(regmodel#(CHANNELS) m_regmodel);
        this.m_regmodel = m_regmodel;

        for (int unsigned it = 0; it < CHANNELS; it++) begin
            uvm_reg_field_cb::add(this.m_regmodel.channel[it].control.dma_enable, m_status_cbs[it]);
        end
    endfunction


    function dma_model_packet get_pcie_transaction(logic [64-1:0] addr, int unsigned packet_byte_size, logic [32-1:0] data []);
        dma_model_packet rq;

        rq = dma_model_packet::type_id::create(this.get_full_name);

        rq.at                = 0;
        rq.traffic_class     = 0;
        rq.id_based_ordering = 0;
        rq.relaxed_ordering  = 0;
        rq.tag               = 0;
        rq.requester_id      = 0;
        rq.ep                = 0;
        rq.td                = 0;
        rq.th                = 0;
        rq.ph                = 0;
        rq.no_snoop          = 0;
        rq.address           = addr[64-1:2];

        if (addr[64-1:32] == 0) begin
            rq.fmt = 3'b010;
        end else begin
            rq.fmt = 3'b011;
        end
        rq.pcie_type = 0; //memory write request

        assert(addr[2-1:0] == 0) else `uvm_fatal(this.get_full_name(), $sformatf("\n\tThis model doesnt support counting fbe. lower 2 bits of addres heve to zero"));
        // FBE
        rq.fbe = '1;
        // LBE
        case (packet_byte_size % 4)
            0:
                rq.lbe = 4'b1111;
            1:
                rq.lbe = 4'b0001;
            2:
                rq.lbe = 4'b0011;
            3:
                rq.lbe = 4'b0111;
        endcase
        rq.length = (packet_byte_size + 3)/4;
        rq.data   = data;

        if (rq.length == 1) begin
            rq.fbe &= rq.lbe;
            rq.lbe = 0;
        end

        return rq;
    endfunction

    function void get_dma_header(logic [16-1:0] frame_pointer, logic[16-1:0] frame_length, logic [24-1:0] meta, bit valid_bit, output logic[32-1 : 0] header[2]);
        logic [64-1:0] out_hdr;

        out_hdr = {meta, 7'b0, valid_bit, frame_pointer, frame_length};
        header = {<<32{out_hdr}};
    endfunction


    function void get_data_last(logic[32-1 : 0] packet[], int unsigned f_start, int unsigned f_end, output logic[32-1 : 0] out[]);
        out = new [f_end - f_start];
        for (int unsigned it = 0; it < f_end - f_start; it++) begin
            out[it] = packet[f_start + it];
        end
    endfunction

    task packet_send(logic [ITEM_WIDTH-1:0] packet[], time start_time, int unsigned channel, logic [24-1:0] meta);
        string                     msg;
        int unsigned               rem ;
        dma_model_packet           packet_output;
        int unsigned               it;
        // Packet end is rounded up to whole dwords
        logic [32-1 : 0]           packet_end[] = new [((packet.size() % BLOCK_SIZE_BYTES)+3)/4];
        logic[32-1 : 0]            pcie_packet[];
        logic[32-1 : 0]            packet_hdr[2];
        int unsigned               packet_pointer_start;
        int unsigned               parts;
        logic [64-1:0]             addr;

        packet_pointer_start = m_data[channel].data_ptr;
        pcie_packet = new[(packet.size()+3)/4];
        for (it = 0; it < (packet.size()+3)/4; it++) begin
            pcie_packet[it] = {<<8{packet[it*4 +: 4]}};
        end

        parts = (packet.size() + BLOCK_SIZE_BYTES-1)/BLOCK_SIZE_BYTES;
        //SEND PARTS OF PACKETS EXCEPT LAST PART
        for (it = 0; it < (parts-1); it++) begin
            addr = m_regmodel.channel[channel].data_base.get() + (m_data[channel].data_ptr*BLOCK_SIZE_BYTES);
            m_data[channel].data_ptr = (m_data[channel].data_ptr + 1) & m_regmodel.channel[channel].data_mask.get();

            packet_output = get_pcie_transaction(addr, BLOCK_SIZE_BYTES, pcie_packet[it*BLOCK_SIZE_DWS +: BLOCK_SIZE_DWS]);
            packet_output.packet_num   = m_pkt_cntr_total_chan[channel];
            packet_output.data_packet  = 1;
            packet_output.channel      = channel;
            packet_output.part_num     = parts;
            packet_output.part         = it+1;
            packet_output.start[this.get_full_name()]  = start_time;
            m_pcie_rq_mfb_port.write(packet_output);
        end

        //SEND LAST PART OF PACKET
        addr = m_regmodel.channel[channel].data_base.get() + (m_data[channel].data_ptr*BLOCK_SIZE_BYTES);
        m_data[channel].data_ptr = (m_data[channel].data_ptr + 1) & m_regmodel.channel[channel].data_mask.get();

        get_data_last(pcie_packet, it*BLOCK_SIZE_DWS, (packet.size()+3)/4, packet_end);
        rem = packet.size() % BLOCK_SIZE_BYTES;
        packet_output = get_pcie_transaction(addr, rem == 0 ? 128 : rem, packet_end);
        packet_output.packet_num   = m_pkt_cntr_total_chan[channel];
        packet_output.data_packet  = 1;
        packet_output.channel      = channel;
        packet_output.part_num     = parts;
        packet_output.part         = parts;
        packet_output.start[this.get_full_name()]  = start_time;
        m_pcie_rq_mfb_port.write(packet_output);

        msg = {msg, $sformatf("\nSend last segment of packet (CH %d, no. %d):\n", channel, parts)};
        msg = {msg, $sformatf("\tStart pointer in input: %d \n", it*BLOCK_SIZE_DWS)};
        msg = {msg, $sformatf("\tLength of input: %d Bytes (rounded: %d DWs) \n", packet.size(), (packet.size()+3)/4)};
        msg = {msg, $sformatf("\tLast block length: actual -, requred %d Bytes\n", packet.size() % BLOCK_SIZE_BYTES)};
        msg = {msg, $sformatf("\tPacket data:\n%s\n", packet_output.convert_data2string())};
        `uvm_info(this.get_full_name(), msg, UVM_HIGH);

        //SEND DMA HEADER
        addr = m_regmodel.channel[channel].hdr_base.get() + (m_data[channel].hdr_ptr*8);
        m_data[channel].hdr_ptr = (m_data[channel].hdr_ptr + 1) & m_regmodel.channel[channel].hdr_mask.get();

        get_dma_header(packet_pointer_start, packet.size(), meta, m_data[channel].vld_bit, packet_hdr);
        packet_output = get_pcie_transaction(addr, 8, packet_hdr);
        packet_output.packet_num   = m_pkt_cntr_total_chan[channel];
        packet_output.data_packet  = 0;
        packet_output.channel      = channel;
        packet_output.part_num     = 1;
        packet_output.part         = 1;
        packet_output.start[this.get_full_name()]  = start_time;
        m_pcie_rq_mfb_port.write(packet_output);

        // It the header pointer overflows, flip the valid bit
        if (m_data[channel].hdr_ptr == 0) begin
            m_data[channel].vld_bit = ~m_data[channel].vld_bit;
        end
    endtask

    task get_input();
        uvm_logic_vector::sequence_item#(USER_META_WIDTH)  tr_meta;
        packet_info                                        info;

        forever begin
            m_usr_mfb_meta_fifo.get(tr_meta);
            {info.packet_size, info.channel, info.meta} = tr_meta.data;
            info.input_time = $time();

            m_input_meta.push_back(info);
        end
    endtask

    function void build_phase(uvm_phase phase);
        m_pkt_disc_mvb_subs = dma_model_accept#(CHANNELS)::type_id::create("m_pkt_disc_mvb_subs", this);

        m_probe_discard = disc_probe_cbs::type_id::create("m_probe_discard", this);
        uvm_probe::pool::get_global_pool().get({ "probe_event_component_", "testbench.DUT_U.VHDL_DUT_U", ".probe_discard" }).add_callback(m_probe_discard);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_logic_vector_array::sequence_item #(ITEM_WIDTH) tr;
        string                                              msg;
        int unsigned                                        compare;
        int unsigned                                        soft_compare;
        logic                                               dma_discard;
        packet_info                                         info;
        logic                                               pkt_drop;

        fork
            get_input();
        join_none

        forever begin
            //first get metadata. Because this is relevat for checking comparability of packet
            wait (m_input_meta.size() != 0);
            info = m_input_meta.pop_front();

            m_probe_discard.get({pkt_drop});

            //get packet
            m_usr_mfb_data_fifo.get(tr);
            m_pkt_cntr_total_chan[info.channel]++;

            //Check if packet have been discared of send when starting or stopping channel
            wait (m_pkt_disc_mvb_subs.fifo.size() != 0);
            dma_discard = m_pkt_disc_mvb_subs.fifo.pop_front();

            // Check whether packet is accepted or not
            if (pkt_drop) begin
                m_pkt_disc_cntr[info.channel]++;
                m_bytes_disc_cntr[info.channel] += tr.data.size();
                 msg = $sformatf("\n\t\nPacket Dropped:\n RX CHANNEL: %0d\n META: %h\n PACKET SIZE: %0d\n%s", info.channel, info.meta, info.packet_size, tr.convert2string());
                `uvm_info(this.get_full_name(), msg,  UVM_MEDIUM);
            end else begin
                m_pkt_sent_cntr[info.channel]++;
                m_bytes_sent_cntr[info.channel] += tr.data.size();
                msg = $sformatf("\n\t\nPacket Accepted:\n RX CHANNEL: %0d\n META: %h\n PACKET SIZE: %0d\n%s", info.channel, info.meta, info.packet_size, tr.convert2string());
                `uvm_info(this.get_full_name(), msg,  UVM_MEDIUM);
                packet_send(tr.data, info.input_time, info.channel, info.meta);
            end
        end
    endtask

    function void extract_phase(uvm_phase phase);
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            m_pkt_cntrs_storage.pkt_sent_cntr[it]   = m_pkt_sent_cntr[it];
            m_pkt_cntrs_storage.bytes_sent_cntr[it] = m_bytes_sent_cntr[it];
            m_pkt_cntrs_storage.pkt_disc_cntr[it]   = m_pkt_disc_cntr[it];
            m_pkt_cntrs_storage.bytes_disc_cntr[it] = m_bytes_disc_cntr[it];
        end
    endfunction
endclass
