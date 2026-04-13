// sequence_mac_check_configuration.sv: Configuration sequence for MAC Check subcomponent of RX MAC Lite
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

// TODO: Multi-channel support

class sequence_mac_check_configuration #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(uvm_network_mod_env::sequence_mac_check_configuration #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH))
    `uvm_declare_p_sequencer(uvm_network_mod_env::sequencer_port #(ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH, ITEM_WIDTH, REGIONS, REGION_SIZE, BLOCK_SIZE, ETH_PORT_CHAN, MI_DATA_WIDTH, MI_ADDR_WIDTH))

    localparam int unsigned RX_MAC_COUNT = 16;

    typedef enum bit[2-1 : 0] {
        ALL_PASS                  = 2'h0,
        ONLY_VALID                = 2'h1,
        VALID_AND_BCAST           = 2'h2,
        VALID_AND_BCAST_AND_MCAST = 2'h3
    } mode_e;

    rand mode_e         mode;
    rand bit [48-1 : 0] addresses[$ : RX_MAC_COUNT];

    constraint c_mode { addresses.size() == 0 -> mode == ALL_PASS; }
    constraint c_addresses {
        addresses.size() <= RX_MAC_COUNT;
        unique { addresses };
    }

    // Constructor
    function new(string name = "sequence_mac_check_configuration");
        super.new(name);
    endfunction

    task body;
        configure_addresses();
        configure_mode();
    endtask

    protected virtual task configure_addresses();
        string msg = "";
        uvm_status_e status;

        foreach (addresses[i]) begin
            p_sequencer.regmodel.channel[0].rx_mac.mac[i].write(status, { 1'b1, addresses[i] });
            msg = {msg, $sformatf("\n\t\tMAC[%0d] : %h", i, addresses[i])};
        end

        `uvm_info(p_sequencer.get_full_name(), {"\n\tWrite MAC ADDRESS:", msg}, UVM_LOW);
    endtask

    protected virtual task configure_mode();
        uvm_status_e status;
        p_sequencer.regmodel.channel[0].rx_mac.mac_check.write(status, mode);
    endtask

endclass
