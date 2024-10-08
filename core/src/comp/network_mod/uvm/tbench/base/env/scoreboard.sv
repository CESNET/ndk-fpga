//-- scoreboard.sv: scoreboard 
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class scoreboard #(ETH_CORE_ARCH, ETH_PORTS, int unsigned ETH_PORT_SPEED[ETH_PORTS-1:0], int unsigned ETH_PORT_CHAN[ETH_PORTS-1:0], REGIONS, ITEM_WIDTH, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_network_mod_env::scoreboard #(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, REGIONS, ITEM_WIDTH, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH));

    //eports
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) eth_rx_data[ETH_PORTS];
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(6))                eth_rx_hdr[ETH_PORTS];
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) eth_tx_data[ETH_PORTS];
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(1))                eth_tx_hdr[ETH_PORTS];

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) usr_rx_data[ETH_PORTS];
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(ETH_TX_HDR_WIDTH)) usr_rx_hdr[ETH_PORTS];
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) usr_tx_data[ETH_PORTS];
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(ETH_RX_HDR_WIDTH)) usr_tx_hdr[ETH_PORTS];

    //comparators
    protected uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) m_eth_tx_data[ETH_PORTS];
    protected uvm_common::comparer_ordered #(uvm_logic_vector::sequence_item#(1))                m_eth_tx_hdr[ETH_PORTS];

    protected uvm_common::comparer_ordered #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) m_usr_tx_data[ETH_PORTS];
    protected uvm_network_mod_env::comparer_tx_hdr#(ETH_RX_HDR_WIDTH)                            m_usr_tx_hdr[ETH_PORTS];

    //METERS
    protected uvm_logic_vector_array::meter#(ITEM_WIDTH) m_eth_rx_meter[ETH_PORTS];
    protected uvm_logic_vector_array::meter#(ITEM_WIDTH) m_eth_tx_meter[ETH_PORTS];
    protected uvm_logic_vector_array::meter#(ITEM_WIDTH) m_usr_rx_meter[ETH_PORTS];
    protected uvm_logic_vector_array::meter#(ITEM_WIDTH) m_usr_tx_meter[ETH_PORTS];

    protected model #(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, REGIONS, ITEM_WIDTH, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH) m_model;
    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            eth_rx_data[it] = new($sformatf("eth_rx_data_%0d", it), this);
            eth_rx_hdr [it] = new($sformatf("eth_rx_hdr_%0d", it), this);
            eth_tx_data[it] = new($sformatf("eth_tx_data_%0d", it), this);
            eth_tx_hdr [it] = new($sformatf("eth_tx_hdr_%0d", it), this);

            usr_rx_data[it] = new($sformatf("usr_rx_data_%0d", it), this);
            usr_rx_hdr [it] = new($sformatf("usr_rx_hdr_%0d", it), this);
            usr_tx_data[it] = new($sformatf("usr_tx_data_%0d", it), this);
            usr_tx_hdr [it] = new($sformatf("usr_tx_hdr_%0d", it), this);
        end
    endfunction

    function int unsigned success();
        int unsigned ret = 1;
         for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            ret &= m_eth_tx_data[it].success();
            ret &= m_eth_tx_hdr [it].success();
            ret &= m_usr_tx_data[it].success();
            ret &= m_usr_tx_hdr [it].success();
        end
        return ret;
    endfunction

    function int unsigned used();
         int unsigned ret = 0;
         for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            ret |= (m_eth_tx_data[it].used() != 0);
            ret |= (m_eth_tx_hdr [it].used() != 0);
            ret |= (m_usr_tx_data[it].used() != 0);
            ret |= (m_usr_tx_hdr [it].used() != 0);
        end

        ret |= m_model.used();
        return ret;
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            m_eth_tx_data[it] = uvm_common::comparer_ordered#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))::type_id::create($sformatf("m_eth_tx_data_%0d", it), this); 
            m_eth_tx_hdr [it] = uvm_common::comparer_ordered#(uvm_logic_vector::sequence_item#(1))::type_id::create($sformatf("m_eth_tx_hdr_%0d", it), this);

            m_usr_tx_data[it] = uvm_common::comparer_ordered#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))::type_id::create($sformatf("m_usr_tx_data_%0d", it), this);
            m_usr_tx_hdr [it] = uvm_network_mod_env::comparer_tx_hdr#(ETH_RX_HDR_WIDTH)::type_id::create($sformatf("m_usr_tx_hdr_%0d", it), this);

            //METERS
            m_eth_rx_meter[it] = uvm_logic_vector_array::meter#(ITEM_WIDTH)::type_id::create($sformatf("m_eth_rx_meter_%0d", it), this);
            m_eth_tx_meter[it] = uvm_logic_vector_array::meter#(ITEM_WIDTH)::type_id::create($sformatf("m_eth_tx_meter_%0d", it), this);
            m_usr_rx_meter[it] = uvm_logic_vector_array::meter#(ITEM_WIDTH)::type_id::create($sformatf("m_usr_rx_meter_%0d", it), this);
            m_usr_tx_meter[it] = uvm_logic_vector_array::meter#(ITEM_WIDTH)::type_id::create($sformatf("m_usr_tx_meter_%0d", it), this);
        end

        m_model = model#(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, REGIONS, ITEM_WIDTH, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH)::type_id::create("m_model", this);
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            eth_rx_data[it].connect(m_model.eth_rx_data[it].analysis_export);
            eth_rx_hdr [it].connect(m_model.eth_rx_hdr [it].analysis_export);
            m_model.eth_tx_data[it].connect(m_eth_tx_data[it].analysis_imp_model);
            m_model.eth_tx_hdr [it].connect(m_eth_tx_hdr [it].analysis_imp_model);
            eth_tx_data[it].connect(m_eth_tx_data[it].analysis_imp_dut);
            eth_tx_hdr [it].connect(m_eth_tx_hdr [it].analysis_imp_dut);

            usr_rx_data[it].connect(m_model.usr_rx_data[it].analysis_export);
            usr_rx_hdr [it].connect(m_model.usr_rx_hdr [it].analysis_export);
            m_model.usr_tx_data[it].connect(m_usr_tx_data[it].analysis_imp_model);
            m_model.usr_tx_hdr [it].connect(m_usr_tx_hdr [it].analysis_imp_model);
            usr_tx_data[it].connect(m_usr_tx_data[it].analysis_imp_dut);
            usr_tx_hdr [it].connect(m_usr_tx_hdr [it].analysis_imp_dut);


            eth_rx_data[it].connect(m_eth_rx_meter[it].analysis_export);
            eth_tx_data[it].connect(m_eth_tx_meter[it].analysis_export);
            usr_rx_data[it].connect(m_usr_rx_meter[it].analysis_export);
            usr_tx_data[it].connect(m_usr_tx_meter[it].analysis_export);

        end
    endfunction

    function void report_phase(uvm_phase phase);
        string msg = "";

        msg = {msg, $sformatf("\n\tSuccess %0d Used %0d", this.success(), this.used())};
        if (this.success() && this.used() == 0) begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAILED       ----\n\t---------------------------------------"}, UVM_NONE)
        end
    endfunction

endclass
