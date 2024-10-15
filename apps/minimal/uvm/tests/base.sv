/*
 * file       : test.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description:  base test
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class base#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
            REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_test;
    typedef uvm_component_registry#(test::base#(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
                                                REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH),
                                               "test::base") type_id;
    localparam DMA_RX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_TX_CHANNELS);
    localparam DMA_TX_MVB_WIDTH = $clog2(DMA_PKT_MTU+1)+DMA_HDR_META_WIDTH+$clog2(DMA_RX_CHANNELS) + 1;

    //top env for sychnronization
    //uvm_app_core_top_agent::agent#(TR_TYPE, ITEM_WIDTH, META_WIDTH)

    typedef uvm_app_core_top_agent::sequence_eth_item#(2**8, 16, MFB_ITEM_WIDTH)                                                   sequence_item_eth_rx;
    typedef uvm_app_core_top_agent::sequence_dma_item#(DMA_TX_CHANNELS, $clog2(DMA_PKT_MTU+1), DMA_HDR_META_WIDTH, MFB_ITEM_WIDTH) sequence_item_dma_rx;

    uvm_app_core_minimal::env #(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
            REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH) m_env;

    logic event_reset;

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
        m_env = uvm_app_core_minimal::env #(ETH_STREAMS, ETH_CHANNELS, ETH_PKT_MTU, ETH_RX_HDR_WIDTH, ETH_TX_HDR_WIDTH, DMA_STREAMS, DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_HDR_META_WIDTH, DMA_PKT_MTU,
            REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MEM_PORTS, MEM_ADDR_WIDTH, MEM_BURST_WIDTH, MEM_DATA_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_env", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        m_env.delay_max_set(10ms, 10ms);
    endfunction

    virtual task run_reset(uvm_phase phase);
        uvm_reset::sequence_reset reset;
        uvm_reset::sequence_run   run;

        reset = uvm_reset::sequence_reset::type_id::create("reset_reset");
        run   = uvm_reset::sequence_run::type_id::create("reset_run");
        run.length_min = 1000;
        run.length_max = 2000;

        //
        forever begin
            int unsigned reset_repeat;
            event_reset = 1'b1;
            //reset.set_starting_phase(phase);
            void'(reset.randomize());
            reset.start(m_env.m_resets_gen.m_sequencer);

            event_reset  = 1'b0;
            reset_repeat = $urandom_range(5,10);
            //for (int unsigned it = 0; it < reset_repeat; it++) begin
            forever begin
                void'(run.randomize());
                run.start(m_env.m_resets_gen.m_sequencer);
            end
        end
    endtask

    task run_mem();
        uvm_avmm::sequence_library_master #(MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH) mem_seq[MEM_PORTS];

        for (int unsigned it = 0; it < MEM_PORTS; it ++) begin
            mem_seq[it] = uvm_avmm::sequence_library_master #(MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH)::type_id::create($sformatf("mem_seq_%0d", it), this);;
        end

        for (int unsigned it = 0; it < MEM_PORTS; it ++) begin
            fork
                automatic int unsigned index = it;
                forever begin
                    assert(mem_seq[index].randomize()) else begin `uvm_fatal(this.get_full_name(), $sfomratf("Cannot randomize memory sequence %0d", index)) end
                    mem_seq[index].start(m_env.m_sequencer.m_memory[index]);
                end
            join_none
        end
    endtask

    virtual task dirver_sequence();
        uvm_app_core_minimal::reg_sequence#(ETH_STREAMS, ETH_CHANNELS, DMA_STREAMS, DMA_RX_CHANNELS) seq;

        seq = uvm_app_core_minimal::reg_sequence#(ETH_STREAMS, ETH_CHANNELS, DMA_STREAMS, DMA_RX_CHANNELS)::type_id::create("seq", this);

        seq.m_regmodel = m_env.m_regmodel.m_regmodel;
        seq.start(null);
    endtask

    virtual task run_phase(uvm_phase phase);
        uvm_app_core::sequence_tsu  tsu_seq;
        uvm_app_core::sequence_main#(DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                        ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH) main_seq;
        uvm_app_core::sequence_stop#(DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                        ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH) stop_seq;
        time end_time;
        int rdy2end;

        main_seq = uvm_app_core::sequence_main#(DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                       ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH)::type_id::create("main_seq", m_env.m_sequencer);
        stop_seq = uvm_app_core::sequence_stop#(DMA_RX_CHANNELS, DMA_TX_CHANNELS, DMA_PKT_MTU, DMA_HDR_META_WIDTH, DMA_STREAMS, ETH_TX_HDR_WIDTH,  MFB_ITEM_WIDTH,
                       ETH_STREAMS, REGIONS, MFB_REG_SIZE, MFB_BLOCK_SIZE, MEM_PORTS, MEM_ADDR_WIDTH, MEM_DATA_WIDTH, MEM_BURST_WIDTH)::type_id::create("stop_seq", m_env.m_sequencer);

        phase.raise_objection(this);

        // RUN RESET
        fork
            run_reset(phase);
        join_none;


        // RUN TSU
        tsu_seq = uvm_app_core::sequence_tsu::type_id::create("tsu_seq", m_env.m_tsu.m_sequencer);
        tsu_seq.randomize();
        fork
            tsu_seq.start(m_env.m_tsu.m_sequencer);
        join_none;

        ////configure egent
        wait(event_reset == 1'b0);
        for (int unsigned it = 0; it < 3; it++) begin

            //RUN RIVER SEQUENCE ONLY IF RESET IS NOT SET
            dirver_sequence();
            #(200ns);

            for (int unsigned it = 0; it < 5; it++) begin
                assert(main_seq.randomize()) else `uvm_fatal(m_env.m_sequencer.get_full_name(), "\n\tCannot randomize main sequence");
                main_seq.time_start = tsu_seq.time_start;
                main_seq.start(m_env.m_sequencer);
            end

            assert(stop_seq.randomize()) else `uvm_fatal(m_env.m_sequencer.get_full_name(), "\n\tCannot randomize main sequence");

            fork
                stop_seq.start(m_env.m_sequencer);
            join_none;

            end_time = $time() + 50ms; // Prevents verification from freezing after a very long time!
            rdy2end = 0;
            while (end_time > $time() && rdy2end < 5) begin
                // The check of the number of incomplete packets in the verification must pass repeatedly!
                if (m_env.used() == 0) begin
                    rdy2end++;
                end else begin
                    rdy2end = 0;
                end
                #(1us);
            end
            if (m_env.used() != 0) begin
                `uvm_warning(this.get_full_name(), $sformatf("\n\tUSED(%0d) sould be zero.\n\tDuring reconfiguration, There is some data in design", m_env.used()));
            end

            stop_seq.done_set();
        end

        phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass
