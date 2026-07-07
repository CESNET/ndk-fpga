/*
 * file       : test.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description:  base test
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class full_speed #(
    int unsigned ETH_STREAMS,
    int unsigned ETH_CHANNELS,
    int unsigned ETH_PKT_MTU,
    int unsigned ETH_RX_HDR_WIDTH,
    int unsigned ETH_TX_HDR_WIDTH,
    int unsigned DMA_STREAMS,
    int unsigned DMA_RX_CHANNELS,
    int unsigned DMA_TX_CHANNELS,
    int unsigned DMA_HDR_META_WIDTH,
    int unsigned DMA_PKT_MTU,
    int unsigned REGIONS,
    int unsigned MFB_REG_SIZE,
    int unsigned MFB_BLOCK_SIZE,
    int unsigned MFB_ITEM_WIDTH,
    int unsigned MEM_PORTS,
    int unsigned MEM_ADDR_WIDTH,
    int unsigned MEM_BURST_WIDTH,
    int unsigned MEM_DATA_WIDTH,
    int unsigned MI_DATA_WIDTH,
    int unsigned MI_ADDR_WIDTH
) extends base #(
    ETH_STREAMS,
    ETH_CHANNELS,
    ETH_PKT_MTU,
    ETH_RX_HDR_WIDTH,
    ETH_TX_HDR_WIDTH,
    DMA_STREAMS,
    DMA_RX_CHANNELS,
    DMA_TX_CHANNELS,
    DMA_HDR_META_WIDTH,
    DMA_PKT_MTU,
    REGIONS,
    MFB_REG_SIZE,
    MFB_BLOCK_SIZE,
    MFB_ITEM_WIDTH,
    MEM_PORTS,
    MEM_ADDR_WIDTH,
    MEM_BURST_WIDTH,
    MEM_DATA_WIDTH,
    MI_DATA_WIDTH,
    MI_ADDR_WIDTH
);
    typedef uvm_component_registry #(
        test::full_speed #(
            ETH_STREAMS,
            ETH_CHANNELS,
            ETH_PKT_MTU,
            ETH_RX_HDR_WIDTH,
            ETH_TX_HDR_WIDTH,
            DMA_STREAMS,
            DMA_RX_CHANNELS,
            DMA_TX_CHANNELS,
            DMA_HDR_META_WIDTH,
            DMA_PKT_MTU,
            REGIONS,
            MFB_REG_SIZE,
            MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH,
            MEM_PORTS,
            MEM_ADDR_WIDTH,
            MEM_BURST_WIDTH,
            MEM_DATA_WIDTH,
            MI_DATA_WIDTH,
            MI_ADDR_WIDTH
        ),
        "test::full_speed"
    ) type_id;

    function new (string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    static function type_id get_type();
        return type_id::get();
    endfunction

    function string get_type_name();
        return get_type().get_type_name();
    endfunction

    function void build_phase(uvm_phase phase);
        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            uvm_logic_vector_array_mfb::sequence_lib_rx #(
                REGIONS,
                MFB_REG_SIZE,
                MFB_BLOCK_SIZE,
                MFB_ITEM_WIDTH,
                0
            )::type_id::set_inst_override(
                uvm_logic_vector_array_mfb::sequence_lib_rx_speed #(
                    REGIONS,
                    MFB_REG_SIZE,
                    MFB_BLOCK_SIZE,
                    MFB_ITEM_WIDTH,
                    0
                )::get_type(),
                {".m_env.m_eth_mfb_rx_", it_num, ".*"},
                this
            );

            uvm_logic_vector_mvb::sequence_lib_rx #(
                REGIONS,
                ETH_RX_HDR_WIDTH
            )::type_id::set_inst_override(
                uvm_logic_vector_mvb::sequence_lib_rx_speed #(
                    REGIONS,
                    ETH_RX_HDR_WIDTH
                )::get_type(),
                {"m_env.m_eth_mvb_rx_", it_num, ".*"},
                this
            );

            uvm_mfb::sequence_lib_tx
                #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH)::type_id::set_inst_override(
                uvm_mfb::sequence_lib_tx_speed
                    #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH)::get_type(),
                {".m_env.m_eth_mfb_tx_", it_num, ".*"},
                this
            );

        end

        for (int unsigned it = 0; it < DMA_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);

            uvm_logic_vector_array_mfb::sequence_lib_rx #(
                REGIONS,
                MFB_REG_SIZE,
                MFB_BLOCK_SIZE,
                MFB_ITEM_WIDTH,
                0
            )::type_id::set_inst_override(
                uvm_logic_vector_array_mfb::sequence_lib_rx_speed #(
                    REGIONS,
                    MFB_REG_SIZE,
                    MFB_BLOCK_SIZE,
                    MFB_ITEM_WIDTH,
                    0
                )::get_type(),
                {"m_env.m_dma_mfb_rx_", it_num, ".*"},
                this
            );

            uvm_logic_vector_mvb::sequence_lib_rx #(
                REGIONS,
                DMA_RX_MVB_WIDTH
            )::type_id::set_inst_override(
                uvm_logic_vector_mvb::sequence_lib_rx_speed #(REGIONS, DMA_RX_MVB_WIDTH)::get_type(),
                {"m_env.m_dma_mvb_rx_", it_num, ".*"},
                this
            );


            uvm_mfb::sequence_lib_tx
                #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::set_inst_override(
                uvm_mfb::sequence_lib_tx_speed #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::get_type(),
                {"m_env.m_dma_mfb_tx_", it_num, ".*"},
                this
            );

            uvm_mvb::sequence_lib_tx #(REGIONS, DMA_TX_MVB_WIDTH)::type_id::set_inst_override(
                uvm_mvb::sequence_lib_tx_speed #(REGIONS, DMA_TX_MVB_WIDTH)::get_type(),
                {"m_env.m_dma_mvb_tx_", it_num, ".*"},
                this
            );
        end

        super.build_phase(phase);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        m_env.delay_max_set(10ms, 10ms);
    endfunction
endclass
