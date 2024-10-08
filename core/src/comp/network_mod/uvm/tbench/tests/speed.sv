//-- base.sv: basig test
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class speed #(
    string ETH_CORE_ARCH,

    int unsigned ETH_PORTS,
    int unsigned ETH_PORT_SPEED[ETH_PORTS-1:0],
    int unsigned ETH_PORT_CHAN[ETH_PORTS-1 : 0],
    int unsigned ETH_TX_HDR_WIDTH,
    int unsigned ETH_RX_HDR_WIDTH,

    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,

    int unsigned MI_DATA_WIDTH,
    int unsigned MI_ADDR_WIDTH
) extends base #(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH);
    typedef uvm_component_registry#(test::speed #(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH), "test::speed") type_id;

    localparam time timeout_max = 200us;
    
    uvm_network_mod_env::env #(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDR_WIDTH) m_env;

    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    static function type_id get_type();
        return type_id::get();
    endfunction

    function string get_type_name();
        return get_type().get_type_name();
    endfunction

    function void build_phase(uvm_phase phase);
        // USR
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            uvm_logic_vector_array_mfb::sequence_lib_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, ETH_TX_HDR_WIDTH
                    )::type_id::set_inst_override(uvm_logic_vector_array_mfb::sequence_lib_rx_speed#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, ETH_TX_HDR_WIDTH
                )::get_type(),{this.get_full_name(), $sformatf(".m_env.m_usr_rx_%0d.*", it)});

            uvm_mfb::sequence_lib_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)
                    ::type_id::set_inst_override(uvm_mfb::sequence_lib_tx_speed#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)
                ::get_type(),{this.get_full_name(), $sformatf(".m_env.m_usr_tx_data_%0d.*", it)});

            uvm_mvb::sequence_lib_tx#(REGIONS, ETH_RX_HDR_WIDTH)::type_id::set_inst_override(uvm_mvb::sequence_lib_tx_speed#(REGIONS, ETH_RX_HDR_WIDTH)
                ::get_type(),{this.get_full_name(), $sformatf(".m_env.m_usr_tx_hdr_%0d.*", it)});
        end

        // ETH
        if (ETH_CORE_ARCH == "E_TILE") begin
            for (int unsigned it = 0; it < ETH_PORTS; it++) begin
                uvm_logic_vector_array_avst::sequence_lib_rx#(ETH_PORT_CHAN[0], 1, REGION_SIZE * BLOCK_SIZE, ITEM_WIDTH, 6, 0)
                        ::type_id::set_inst_override(uvm_logic_vector_array_avst::sequence_lib_rx_speed#(ETH_PORT_CHAN[0], 1, REGION_SIZE * BLOCK_SIZE, ITEM_WIDTH, 6, 0)
                    ::get_type(),{this.get_full_name(), $sformatf(".m_env.m_eth_rx_%0d.*", it)});

                uvm_avst::sequence_lib_tx#(ETH_PORT_CHAN[0], 1, REGION_SIZE * BLOCK_SIZE, ITEM_WIDTH, 1)::type_id::set_inst_override(uvm_avst::sequence_lib_tx_speed#(ETH_PORT_CHAN[0], 1, REGION_SIZE * BLOCK_SIZE, ITEM_WIDTH, 1)
                    ::get_type(),{this.get_full_name(), $sformatf(".m_env.m_eth_tx_%0d.*", it)});
            end
        end
        else if (ETH_CORE_ARCH == "F_TILE") begin
            `uvm_warning(this.get_full_name(), "\n\tSpeed test for Intel F-Tile IP Core connection is not supported.")
        end

        m_env = uvm_network_mod_env::env #(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MI_DATA_WIDTH,
                            MI_ADDR_WIDTH)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    virtual task run_phase(uvm_phase phase);
        time time_start;
        uvm_network_mod_env::virt_sequence_simple#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH) seq;
        uvm_network_mod_env::virt_sequence_stop#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH)   seq_stop;

        seq = uvm_network_mod_env::virt_sequence_simple#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("sequence", m_env.m_sequencer);
        seq.packet_size_set(test::PACKET_SIZE_MIN, test::PACKET_SIZE_MAX);
        assert(seq.randomize());

        //RISE OBJECTION
        phase.raise_objection(this);

        seq.start(m_env.m_sequencer);

        seq_stop = uvm_network_mod_env::virt_sequence_stop#(ETH_PORTS, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("sequence", m_env.m_sequencer);
        assert(seq_stop.randomize());

        fork
            seq_stop.start(m_env.m_sequencer);
        join_none

        ///////////////////
        // Wait to end
        time_start = $time();
        while((time_start + timeout_max) > $time() && m_env.used()) begin
            #(300ns);
        end

        if ((time_start + timeout_max) < $time()) begin
            `uvm_warning(this.get_full_name(), $sformatf("TIMEOUT exeed %0dns ", ($time() - time_start)/1ns));
        end
        phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction

endclass

