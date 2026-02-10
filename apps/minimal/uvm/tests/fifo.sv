/*
 * file       : test.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description:  base test
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class sequence_mfb_rx_full_speed #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) extends uvm_logic_vector_array_mfb::sequence_rx_full_speed #(
    REGIONS,
    REGION_SIZE,
    BLOCK_SIZE,
    ITEM_WIDTH,
    META_WIDTH
);
    `uvm_object_param_utils(
        test::sequence_mfb_rx_full_speed #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)
    )

    function new(string name = "test::sequence_mfb_rx_full_speed");
        super.new(name);
        hl_transactions_min = 1000;
        hl_transactions_max = 20000;
    endfunction
endclass


class sequence_mfb_rx_stop #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) extends uvm_logic_vector_array_mfb::sequence_rx_stop #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `uvm_object_param_utils(test::sequence_mfb_rx_stop #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    function new(string name = "test::sequence_mfb_rx_stop");
        super.new(name);
        hl_transactions_min = 1000;
        hl_transactions_max = 20000;
    endfunction
endclass


class sequence_lib__mfb_rx_fifo #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) extends uvm_logic_vector_array_mfb::sequence_lib_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
    `uvm_object_param_utils(
        test::sequence_lib__mfb_rx_fifo #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)
    )
    `uvm_sequence_library_utils(
        test::sequence_lib__mfb_rx_fifo #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)
    )

  function new(string name = "test::sequence_lib__mfb_rx_fifo");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(uvm_logic_vector_array_mfb::config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(
            test::sequence_mfb_rx_full_speed #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type()
        );
        this.add_sequence(
            test::sequence_mfb_rx_stop #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type()
        );
    endfunction
endclass

class sequence_mvb_full_speed_rx #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_logic_vector_mvb::sequence_full_speed_rx       #(ITEMS, ITEM_WIDTH);
    `uvm_object_param_utils(test::sequence_mvb_full_speed_rx #(ITEMS, ITEM_WIDTH))

    function new(string name = "test::sequence_mvb_full_speed_rx");
        super.new(name);
        hl_transactions_min = 1000;
        hl_transactions_max = 20000;
    endfunction
endclass


class sequence_mvb_stop_rx #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_logic_vector_mvb::sequence_stop_rx #(ITEMS, ITEM_WIDTH);
    `uvm_object_param_utils(test::sequence_mvb_stop_rx #(ITEMS, ITEM_WIDTH))

    function new(string name = "test::sequence_mvb_stop_rx");
        super.new(name);
        hl_transactions_min = 1000;
        hl_transactions_max = 20000;
    endfunction
endclass


class sequence_lib__mvb_rx_fifo #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_logic_vector_mvb::sequence_lib_rx  #(ITEMS, ITEM_WIDTH);
  `uvm_object_param_utils(    test::sequence_lib__mvb_rx_fifo#(ITEMS, ITEM_WIDTH))
  `uvm_sequence_library_utils(test::sequence_lib__mvb_rx_fifo#(ITEMS, ITEM_WIDTH))

  function new(string name = "test::sequence_lib__mvb_rx_fifo");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(uvm_logic_vector_mvb::config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(test::sequence_mvb_full_speed_rx #(ITEMS, ITEM_WIDTH)::get_type());
        this.add_sequence(test::sequence_mvb_stop_rx       #(ITEMS, ITEM_WIDTH)::get_type());
    endfunction
endclass

// TX SEQUENCES
class sequence_mfb_lib_tx_fifo #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) extends uvm_mfb::sequence_lib_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH);
  `uvm_object_param_utils(    test::sequence_mfb_lib_tx_fifo#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))
  `uvm_sequence_library_utils(test::sequence_mfb_lib_tx_fifo#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

  function new(string name = "sequence_lib_tx_speed");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(uvm_mfb::config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(uvm_mfb::sequence_full_speed_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
        this.add_sequence(uvm_mfb::sequence_stop_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
    endfunction
endclass

class sequence_mvb_lib_tx_fifo #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_mvb::sequence_lib_tx#(ITEMS, ITEM_WIDTH);
  `uvm_object_param_utils(    test::sequence_mvb_lib_tx_fifo#(ITEMS, ITEM_WIDTH))
  `uvm_sequence_library_utils(test::sequence_mvb_lib_tx_fifo#(ITEMS, ITEM_WIDTH))

    function new(string name = "sequence_lib_tx_speed");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(uvm_mvb::config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(uvm_mvb::sequence_full_speed_tx#(ITEMS, ITEM_WIDTH)::get_type());
        this.add_sequence(uvm_mvb::sequence_stop_tx#(ITEMS, ITEM_WIDTH)::get_type());
    endfunction
endclass



class fifo #(
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

    typedef uvm_component_registry#(
        test::fifo #(
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
        "test::fifo"
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
                test::sequence_lib__mfb_rx_fifo #(
                    REGIONS,
                    MFB_REG_SIZE,
                    MFB_BLOCK_SIZE,
                    MFB_ITEM_WIDTH,
                    0
                )::get_type(),
                {"m_env.m_eth_mfb_rx_", it_num, ".*"},
                this
            );

             uvm_logic_vector_mvb::sequence_lib_rx #(REGIONS, ETH_RX_HDR_WIDTH)::type_id::set_inst_override(
                test::sequence_lib__mvb_rx_fifo #(REGIONS, ETH_RX_HDR_WIDTH)::get_type(),
                {"m_env.m_eth_mvb_rx_", it_num, ".*"},
                this
            );

            uvm_mfb::sequence_lib_tx #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH)::type_id::set_inst_override(
                sequence_mfb_lib_tx_fifo #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, ETH_TX_HDR_WIDTH)::get_type(),
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
                test::sequence_lib__mfb_rx_fifo #(
                    REGIONS,
                    MFB_REG_SIZE,
                    MFB_BLOCK_SIZE,
                    MFB_ITEM_WIDTH,
                    0
                )::get_type(),
                {"m_env.m_dma_mfb_rx_", it_num, ".*"},
                this
            );

            uvm_logic_vector_mvb::sequence_lib_rx #(REGIONS, DMA_RX_MVB_WIDTH)::type_id::set_inst_override(
                test::sequence_lib__mvb_rx_fifo #(REGIONS, DMA_RX_MVB_WIDTH)::get_type(),
                {"m_env.m_dma_mvb_rx_", it_num, ".*"},
                this
            );

            uvm_mfb::sequence_lib_tx #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::set_inst_override(
                sequence_mfb_lib_tx_fifo #(REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::get_type(),
                {"m_env.m_dma_mfb_tx_", it_num, ".*"},
                this
            );

            uvm_mvb::sequence_lib_tx #(REGIONS, DMA_TX_MVB_WIDTH)::type_id::set_inst_override(
                sequence_mvb_lib_tx_fifo #(REGIONS, DMA_TX_MVB_WIDTH)::get_type(),
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
