//-- regmodel.sv  registre model
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class reg_model_channel extends uvm_reg_block;
    `uvm_object_param_utils(uvm_network_mod_env::reg_model_channel)

    localparam RX_MAC_COUNT = 4;

    rand uvm_rx_mac_lite::regmodel#(RX_MAC_COUNT) rx_mac;
    rand uvm_tx_mac_lite::regmodel                tx_mac;

    function new(string name = "reg_model_channel");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    virtual function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        uvm_reg_frontdoor casted;

        void'($cast(casted, frontdoor.clone()));
        rx_mac.set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        tx_mac.set_frontdoor(casted);
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        rx_mac    = uvm_rx_mac_lite::regmodel#(RX_MAC_COUNT)::type_id::create("rx_mac", , get_full_name());
        tx_mac    = uvm_tx_mac_lite::regmodel::type_id::create("tx_mac", , get_full_name());

        rx_mac.build('h0, bus_width);
        rx_mac.configure(this, "rx_mac");
        tx_mac.build('h0, bus_width);
        tx_mac.configure(this, "tx_mac");

        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        //Add registers to map
        this.default_map.add_submap(tx_mac.default_map, 'h000);
        this.default_map.add_submap(rx_mac.default_map, 'h200);

        this.lock_model();
    endfunction
endclass


class reg_model_port#(ETH_CHANNELS) extends uvm_reg_block;
    `uvm_object_param_utils(uvm_network_mod_env::reg_model_port#(ETH_CHANNELS))

    rand reg_model_channel channel[ETH_CHANNELS];
    
    function new(string name = "reg_model_port");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    virtual function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        for (int unsigned it = 0; it < ETH_CHANNELS; it++) begin
            channel[it].set_frontdoor(frontdoor);
        end
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        for (int unsigned it = 0; it < ETH_CHANNELS; it++) begin
            string name = $sformatf("channel_%0d", it);

            channel[it] = reg_model_channel::type_id::create(name, , get_full_name());
            channel[it].build('h0, bus_width);
            channel[it].configure(this, name);
        end

        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        //Add registers to map
        for(int unsigned it = 0; it < ETH_CHANNELS; it++) begin
            this.default_map.add_submap(channel[it].default_map, it * 'h400);
        end

        this.lock_model();
    endfunction
endclass



class regmodel #(ETH_PORTS, int unsigned ETH_PORT_CHAN[ETH_PORTS-1:0]) extends uvm_reg_block;
    `uvm_object_param_utils(uvm_network_mod_env::regmodel #(ETH_PORTS, ETH_PORT_CHAN))

    rand reg_model_port#(ETH_PORT_CHAN[0]) port[ETH_PORTS];

    function new(string name = "reg_model");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    virtual function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            port[it].set_frontdoor(frontdoor);
        end
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            string name = $sformatf("port_%0d", it);

            port[it] = reg_model_port#(ETH_PORT_CHAN[0])::type_id::create(name, , get_full_name());
            port[it].build(bus_width, bus_width);
            port[it].configure(this, name);
        end

        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        //Add registers to map
        for(int unsigned it = 0; it < ETH_PORTS; it++) begin
            this.default_map.add_submap(port[it].default_map, it * 'h2000);
        end
        this.lock_model();
    endfunction

endclass
