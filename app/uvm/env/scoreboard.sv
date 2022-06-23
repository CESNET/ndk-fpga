/*
 * file       : scoreboard.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: scoreboard compare transactions from DUT and MODEL 
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class mvb2logic#(ITEMS, ITEM_WIDTH) extends uvm_monitor;
    `uvm_component_param_utils(app_core::mvb2logic#(ITEMS, ITEM_WIDTH))

    typedef mvb2logic#(ITEMS, ITEM_WIDTH) this_type;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(ITEM_WIDTH)) analysis_port;
    uvm_analysis_imp #(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH), this_type) analysis_export;


    function new (string name, uvm_component parent);
        super.new(name, parent);
        analysis_port = new("analysis_port", this);
        analysis_export = new("analysis_export", this);
    endfunction

    virtual function void write(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH) tr);
        if (tr.src_rdy == 1'b1 && tr.dst_rdy == 1'b1) begin
            for (int unsigned it = 0; it < ITEMS; it++) begin
                if (tr.vld[it] === 1'b1) begin
                    uvm_logic_vector::sequence_item#(ITEM_WIDTH) send;
                    send = uvm_logic_vector::sequence_item#(ITEM_WIDTH)::type_id::create("send");
                    send.data = tr.data[it];
                    analysis_port.write(send);
                end
            end
        end
    endfunction
endclass

class scoreboard #(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_env;
    `uvm_component_param_utils(app_core::scoreboard#(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    //RESET --
    typedef scoreboard #(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, MI_DATA_WIDTH, MI_ADDR_WIDTH) this_type;
    uvm_analysis_imp_reset#(uvm_reset::sequence_item, this_type) analysis_imp_reset;

    //// ETH I/O
    localparam ETH_TX_LENGTH_WIDTH  = 16;
    localparam ETH_TX_CHANNEL_WIDTH = 8;
    uvm_analysis_export #(uvm_mvb::sequence_item#(REGIONS, ETH_RX_HDR_WIDTH))   eth_mvb_rx[ETH_STREAMS];
    uvm_analysis_export #(uvm_byte_array::sequence_item)                        eth_mfb_rx[ETH_STREAMS];
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(ETH_TX_HDR_WIDTH))   eth_mvb_tx[ETH_STREAMS];
    uvm_analysis_export #(uvm_byte_array::sequence_item)                        eth_mfb_tx[ETH_STREAMS];
    // DMA I/O
    localparam DMA_RX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_TX_CHANNELS);
    localparam DMA_TX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_RX_CHANNELS) + 1;
    uvm_analysis_export #(uvm_mvb::sequence_item#(REGIONS, DMA_RX_MVB_WIDTH))   dma_mvb_rx[DMA_STREAMS];
    uvm_analysis_export #(uvm_byte_array::sequence_item)                        dma_mfb_rx[DMA_STREAMS];
    uvm_analysis_export #(uvm_mvb::sequence_item#(REGIONS, DMA_TX_MVB_WIDTH))   dma_mvb_tx[DMA_STREAMS];
    uvm_analysis_export #(uvm_byte_array::sequence_item)                        dma_mfb_tx[DMA_STREAMS];

    //////////////////////////
    // CONNECTION to internal fifos
    scoreboard_channel_header#(ETH_TX_HDR_WIDTH, 0, 2**ETH_TX_CHANNEL_WIDTH, 2**ETH_TX_LENGTH_WIDTH-1) eth_mvb_cmp[ETH_STREAMS];
    scoreboard_channel_mfb #(uvm_byte_array::sequence_item)                        eth_mfb_cmp[ETH_STREAMS];
    scoreboard_channel_header#(DMA_TX_MVB_WIDTH, DMA_HDR_META_WIDTH, DMA_RX_CHANNELS, DMA_PKT_MTU) dma_mvb_cmp[DMA_STREAMS];
    scoreboard_channel_mfb #(uvm_byte_array::sequence_item)                                            dma_mfb_cmp[DMA_STREAMS];

    /////////////////////////
    // MODEL
    model #(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, MI_DATA_WIDTH, MI_ADDR_WIDTH) m_model;

    ////////////////////////
    // LOCAL VARIABLES
    mvb2logic#(REGIONS, DMA_TX_MVB_WIDTH) m_mvb2logic[DMA_STREAMS]; //convert MVB to logic vector
    local int unsigned errors = 0;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        analysis_imp_reset = new("analysis_imp_reset", this);
    endfunction

    function void build_phase(uvm_phase phase);
        ///////////////
        // ETH BUILD ANALYSIS EXPORTS
        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            eth_mvb_rx[it] = new({"eth_mvb_rx_", it_num}, this);
            eth_mfb_rx[it] = new({"eth_mfb_rx_", it_num}, this);
            eth_mvb_tx[it] = new({"eth_mvb_tx_", it_num}, this);
            eth_mfb_tx[it] = new({"eth_mfb_tx_", it_num}, this);

            eth_mvb_cmp[it] = scoreboard_channel_header#(ETH_TX_HDR_WIDTH, 0, 2**ETH_TX_CHANNEL_WIDTH, 2**ETH_TX_LENGTH_WIDTH-1)::type_id::create({"eth_mvb_cmp_", it_num}, this);
            eth_mvb_cmp[it].prefix_set({"ETH [", it_num, "] header "});

            eth_mfb_cmp[it] = scoreboard_channel_mfb #(uvm_byte_array::sequence_item)::type_id::create({"eth_mfb_cmp_", it_num}, this);
            eth_mfb_cmp[it].prefix_set({"ETH [", it_num, "] packet "});
        end

        ///////////////
        // DMA BUILD ANALYSIS EXPORTS
        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            dma_mvb_rx[it] = new({"dma_mvb_rx_", it_num}, this);
            dma_mfb_rx[it] = new({"dma_mfb_rx_", it_num}, this);
            dma_mvb_tx[it] = new({"dma_mvb_tx_", it_num}, this);
            dma_mfb_tx[it] = new({"dma_mfb_tx_", it_num}, this);

            dma_mvb_cmp[it] = app_core::scoreboard_channel_header#(DMA_TX_MVB_WIDTH, DMA_HDR_META_WIDTH, DMA_RX_CHANNELS, DMA_PKT_MTU)::type_id::create({"dma_mvb_cmp_", it_num}, this);
            dma_mvb_cmp[it].prefix_set({"DMA [", it_num, "] header "});

            dma_mfb_cmp[it] = scoreboard_channel_mfb #(uvm_byte_array::sequence_item)::type_id::create({"dma_mfb_cmp_", it_num}, this);
            dma_mfb_cmp[it].prefix_set({"DMA [", it_num, "] packet "});

            m_mvb2logic[it] = mvb2logic#(REGIONS, DMA_TX_MVB_WIDTH)::type_id::create({"m_mvb2logic_", it_num}, this);
        end

        m_model = model #(ETH_STREAMS, ETH_CHANNELS, ETH_RX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU, REGIONS, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_model", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        ///////////////
        // ETH BUILD ANALYSIS EXPORTS
        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);
            //INPUT TO MODEL
            eth_mvb_rx[it].connect(m_model.eth_mvb_rx[it].analysis_export);
            eth_mfb_rx[it].connect(m_model.eth_mfb_rx[it].analysis_export);
            //INPUT TO SC
            eth_mvb_tx[it].connect(eth_mvb_cmp[it].analysis_imp_dut);
            eth_mfb_tx[it].connect(eth_mfb_cmp[it].analysis_imp_dut);
            m_model.eth_mvb_tx[it].connect(eth_mvb_cmp[it].analysis_imp_model);
            m_model.eth_mfb_tx[it].connect(eth_mfb_cmp[it].analysis_imp_model);
        end

        ///////////////
        // DMA BUILD ANALYSIS EXPORTS
        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);
            // INPUT TO MODEL
            dma_mvb_rx[it].connect(m_model.dma_mvb_rx[it].analysis_export);
            dma_mfb_rx[it].connect(m_model.dma_mfb_rx[it].analysis_export);
            // INPUT TO SCOREBOARD
            //dma_mvb_tx[it].connect(dma_mvb_cmp[it].analysis_imp_dut);
            dma_mvb_tx[it].connect(m_mvb2logic[it].analysis_export);
            m_mvb2logic[it].analysis_port.connect(dma_mvb_cmp[it].analysis_imp_dut);
            dma_mfb_tx[it].connect(dma_mfb_cmp[it].analysis_imp_dut);
            m_model.dma_mvb_tx[it].connect(dma_mvb_cmp[it].analysis_imp_model);
            m_model.dma_mfb_tx[it].connect(dma_mfb_cmp[it].analysis_imp_model);
        end
    endfunction

    function void write_reset(uvm_reset::sequence_item tr);
        static bit previs = 1;
        if (tr.reset === 1'b1) begin
            //print info
            if (previs == 0) begin
                string msg = "";
                $sformat(msg, "\n\tRESET DESIGN scoreboard compared data before reset");
                for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
                    $sformat(msg, "%s\n\t\t ETH [%0d] compared Header %0d Packets %0d", msg, it, eth_mvb_cmp[it].compared, eth_mfb_cmp[it].compared); 
                end

                for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
                    $sformat(msg, "%s\n\t\t DMA [%0d] compared Header %0d Packets %0d", msg, it, dma_mvb_cmp[it].compared, dma_mfb_cmp[it].compared); 
                end
                `uvm_info(this.get_full_name(), msg, UVM_LOW);
            end

            //RESET
            for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
                eth_mvb_cmp[it].flush();
                eth_mfb_cmp[it].flush();
            end

            for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
                dma_mvb_cmp[it].flush();
                dma_mfb_cmp[it].flush();
            end
        end
        previs = tr.reset;
    endfunction


    task watch_dog();
        logic stack;
        int unsigned old_compare_eth_header[ETH_STREAMS] = '{ETH_STREAMS{0}};
        int unsigned old_compare_eth_packet[ETH_STREAMS] = '{ETH_STREAMS{0}};
        int unsigned old_compare_dma_header[DMA_STREAMS] = '{DMA_STREAMS{0}};
        int unsigned old_compare_dma_packet[DMA_STREAMS] = '{DMA_STREAMS{0}};

        forever begin
            do begin
                for (int unsigned it = 0; it < ETH_STREAMS; it ++) begin
                    old_compare_eth_header[it] = eth_mvb_cmp[it].compared;
                    old_compare_eth_packet[it] = eth_mfb_cmp[it].compared; //compare_eth_packet[it];
                end

                for (int unsigned it = 0; it < DMA_STREAMS; it ++) begin
                    old_compare_dma_header[it] = dma_mvb_cmp[it].compared;
                    old_compare_dma_packet[it] = dma_mfb_cmp[it].compared;
                end

                #2000ns; //wait time

                stack = 0;

                for (int unsigned it = 0; it < ETH_STREAMS; it ++) begin
                    stack |= old_compare_eth_header[it] != eth_mvb_cmp[it].compared;
                    stack |= old_compare_eth_packet[it] != eth_mfb_cmp[it].compared;
                end

                for (int unsigned it = 0; it < DMA_STREAMS; it ++) begin
                    stack |= old_compare_dma_header[it] != dma_mvb_cmp[it].compared;
                    stack |= old_compare_dma_packet[it] != dma_mfb_cmp[it].compared;
                end
            end while(stack == 1'b0);
            `uvm_error (this.get_full_name(), "\n\tDesign is probubly stuck\n");
            errors++;
        end
    endtask

    function int unsigned used();
        int unsigned ret = 0;

        for(int it = 0; it < ETH_STREAMS; it++) begin
            ret |= eth_mvb_cmp[it].used();
            ret |= eth_mvb_cmp[it].errors != 0;
            ret |= eth_mfb_cmp[it].used();
            ret |= eth_mfb_cmp[it].errors != 0;
        end

        for(int it = 0; it < DMA_STREAMS; it++) begin
            ret |= dma_mvb_cmp[it].used();
            ret |= dma_mvb_cmp[it].errors != 0;
            ret |= dma_mfb_cmp[it].used();
            ret |= dma_mfb_cmp[it].errors != 0;
        end
        ret |= m_model.used();

        return ret;
    endfunction

    function void report_phase(uvm_phase phase);
        string str = "";

        for(int it = 0; it < ETH_STREAMS; it++) begin
            $swrite(str, "%s\n\tETH[%0d] wait on    %d mvb %d mfb transactions from DUT", str, it, eth_mvb_cmp[it].data_model.size(), eth_mfb_cmp[it].data_model.size());
            $swrite(str, "%s\n\tETH[%0d] unexpected %d mvb %d mfb transactions from DUT", str, it, eth_mvb_cmp[it].data_dut.size(), eth_mfb_cmp[it].data_dut.size());
            $swrite(str, "%s\n\tETH[%0d] copared transaction Headers %0d Packets %d", str, it, eth_mvb_cmp[it].compared, eth_mfb_cmp[it].compared);
        end

        for(int it = 0; it < DMA_STREAMS; it++) begin
            $swrite(str, "%s\n\tDMA[%0d] wait on    %d mvb %d mfb transactions from DUT", str, it, dma_mvb_cmp[it].data_model.size(), dma_mfb_cmp[it].data_model.size());
            $swrite(str, "%s\n\tDMA[%0d] unexpected %d mvb %d mfb transactions from DUT", str, it, dma_mvb_cmp[it].data_dut.size(), dma_mfb_cmp[it].data_dut.size());
            $swrite(str, "%s\n\tDMA[%0d] copared transaction Headers %0d Packets %0d ", str, it,   dma_mvb_cmp[it].compared, dma_mfb_cmp[it].compared);
        end

        $swrite(str, "%s\n\tother errors %0d\n\tModel working %b", str, errors, m_model.used());
        if (errors == 0 && this.used() == 0) begin
            `uvm_info(get_type_name(), {str, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {str, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------"}, UVM_NONE)
        end
    endfunction
endclass
