// model.sv: Model of implementation
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

//In first phase - just one channel
class model #(RX_CHANNELS, PKT_MTU, META_WIDTH,  MFB_ITEM_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_framepacker::model#(RX_CHANNELS, PKT_MTU, META_WIDTH,  MFB_ITEM_WIDTH))

    //Model I/O
    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) data_in;
    uvm_analysis_port #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH))     data_out;

    //TODO: Add these signals for a channel recognition
    // verilog_lint: waive line-length
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #($clog2(RX_CHANNELS) + $clog2(PKT_MTU+1)))              meta_in;
    // verilog_lint: waive line-length
    uvm_analysis_port #(uvm_logic_vector::sequence_item #($clog2(RX_CHANNELS) + $clog2(PKT_MTU+1) + META_WIDTH + 1)) meta_out;
    //Output is in model_item.tag (data_out.tag)

    //Internal signal of FrameShifter component - LAST of SUPERPACKET
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(2)) analysis_export_flow_ctrl[RX_CHANNELS];


    // FIFO to store SUPERPACKET
    // verilog_lint: waive line-length
    protected uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)                     channel_fifo_data[RX_CHANNELS][$];
    // verilog_lint: waive line-length
    protected uvm_logic_vector::sequence_item #($clog2(RX_CHANNELS) + $clog2(PKT_MTU+1))  channel_fifo_meta[RX_CHANNELS][$];
    protected logic [MFB_ITEM_WIDTH-1 : 0] sp_fifo[RX_CHANNELS][$];
    protected int unsigned pkt_num;
    protected int unsigned sp_num_cnt;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        //Input
        data_in   = new("data_in",  this);
        data_out  = new("data_out", this);
        meta_in   = new("meta_in", this);
        meta_out  = new("meta_out", this);

        pkt_num = 0;
        //Output
        for (int unsigned chan = 0; chan < RX_CHANNELS; chan++) begin
            analysis_export_flow_ctrl[chan] = new($sformatf("analysis_export_flow_ctrl_%d", chan), this);
        end

    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (data_in.used() != 0);
        ret |= (meta_in.used() != 0);
        for (int unsigned it = 0; it < RX_CHANNELS; it++) begin
            ret |= (channel_fifo_data[it].size() != 0);
            ret |= (channel_fifo_meta[it].size() != 0);
            ret |= (sp_fifo[it].size() != 0);
        end
        return ret;
    endfunction

    task run_channel(int unsigned channel, uvm_phase phase);
        const string tag = $sformatf("CHANNEL %0d", channel);
        // EOF of SUPERPACKET
        uvm_logic_vector::sequence_item #(2) tr_last;
        logic[$clog2(PKT_MTU+1  )-1 : 0] tx_length;
        logic[$clog2(RX_CHANNELS)-1 : 0] tx_channel;
        logic[META_WIDTH-1 : 0]          tx_meta;
        logic                            tx_discard;
        string msg = "";
        int unsigned chan_pkt_num;
        uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) tr_mfb_in;
        uvm_logic_vector::sequence_item #($clog2(RX_CHANNELS) + $clog2(PKT_MTU+1)) tr_mvb_in;
        int unsigned it;

        forever begin

            wait (channel_fifo_data[channel].size() != 0 && channel_fifo_meta[channel].size());

            tr_mfb_in = channel_fifo_data[channel].pop_front();
            tr_mvb_in = channel_fifo_meta[channel].pop_front();

            chan_pkt_num++;
            //SUPERPACKET assemble
            for (it = 0; it < tr_mfb_in.data.size(); it++) begin
                sp_fifo[channel].push_back(tr_mfb_in.data[it]);
            end
            //pealing
            it = it%8;
            if (it != 0) begin
                for (; it < 8; it++) begin
                    sp_fifo[channel].push_back('x);
                end
            end

            //GET if packet is last
            analysis_export_flow_ctrl[channel].get(tr_last);
            `uvm_info(this.get_full_name(), $sformatf(
                      "Received pakcet %0d\nCHANNEL %0d\n\nEOF:        %0d\nLAST:       %0d\nMODEL_IN:   %0s\n",
                      pkt_num,
                      channel,
                      tr_last.data[0],
                      tr_last.data[1],
                      tr_mfb_in.convert2string()
                      ), UVM_MEDIUM);

            if (tr_last.data[1] == 1) begin
                uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) tr_mfb_out;
                uvm_logic_vector::sequence_item #($clog2(RX_CHANNELS) + $clog2(PKT_MTU+1) + META_WIDTH + 1) tr_mvb_out;

                // verilog_lint: waive line-length
                tr_mfb_out = uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)::type_id::create("tr_mfb_out", this);
                tr_mfb_out.tag  = tag;
                sp_num_cnt++;
                tr_mfb_out.data = sp_fifo[channel];
                sp_fifo[channel].delete();

                // verilog_lint: waive line-length
                tr_mvb_out = uvm_logic_vector::sequence_item #($clog2(RX_CHANNELS) + $clog2(PKT_MTU+1) + META_WIDTH + 1)::type_id::create("tr_mvb_out", this);
                tr_mvb_out.tag  = tag;
                tx_length = tr_mfb_out.data.size();
                tx_meta   = 'x;
                tx_discard = 'x;
                tx_channel = channel;
                tr_mvb_out.data = {tx_length, tx_meta, tx_discard, tx_channel};

                //DEBUG
                msg = $sformatf({"\n**************************************************************************",
                              "\nTIME:               %0t ps",
                              "\nCHANNEL             %0d",
                              "\nSUPERPACKET_NO:     %0d",
                              "\nSUPERPACKET_SIZE:   %0d bytes",
                              "\n**************************************************************************\n"}
                              , $time, channel, sp_num_cnt, tr_mfb_out.data.size());
                //`uvm_info(this.get_full_name(), msg, UVM_MEDIUM);
                data_out.write(tr_mfb_out);
                meta_out.write(tr_mvb_out);
            end
        end
    endtask



    task run_phase(uvm_phase phase);
        uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) tr_mfb_in;
        uvm_logic_vector::sequence_item #($clog2(RX_CHANNELS) + $clog2(PKT_MTU+1)) tr_mvb_in;
        logic[$clog2(PKT_MTU+1  )-1 : 0] rx_length;

        //Channel
        logic[$clog2(RX_CHANNELS)-1 : 0] rx_channel;
        sp_num_cnt = 0;
        pkt_num    = 0;

        for(int unsigned it = 0; it < RX_CHANNELS; it++) begin
            fork
                automatic int index = it;
                run_channel(index, phase);
            join_none;
        end


        forever begin
            int unsigned it;
            // Get input packet
            data_in.get(tr_mfb_in);
            meta_in.get(tr_mvb_in);
            pkt_num++;
            {rx_length, rx_channel} = tr_mvb_in.data;
            assert (rx_length == tr_mfb_in.data.size())
            else begin
                `uvm_fatal(this.get_full_name(), $sformatf(
                           "RX length %0d is different from mfb length %0d\n", rx_length, tr_mfb_in.data.size()));
            end

            channel_fifo_data[rx_channel].push_back(tr_mfb_in);
            channel_fifo_meta[rx_channel].push_back(tr_mvb_in);
        end
    endtask

     function void report_phase(uvm_phase phase);
         string msg = "\n";

         msg = {msg, $sformatf("\tData (%0d) meta (%0d)\n", data_in.used(), meta_in.used())};
         msg = {msg, $sformatf("\tPacket processed %0d megapacket created %0d\n", pkt_num, sp_num_cnt)};
         for (int unsigned it = 0; it < RX_CHANNELS; it++) begin
            msg = {
                msg,
                $sformatf(
                    "\t\tchannel %0d Data (%0d) meta (%0d) internal superpacket data (%0d)\n",
                    it,
                    channel_fifo_data[it].size(),
                    channel_fifo_meta[it].size(),
                    sp_fifo[it].size()
                )
            };
         end
         `uvm_info(this.get_full_name(), msg, UVM_NONE);
    endfunction
endclass
