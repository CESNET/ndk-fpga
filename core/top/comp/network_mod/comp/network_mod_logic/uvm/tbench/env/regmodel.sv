/*
 * file       : mac_reg.sv
 * description: Register model for MAC Lites
 * date       : 2022
 * author     : Daniel Kondys <xkondy00@vutbr.cz>
 *
 * Copyright (C) 2022 CESNET z. s. p. o.
*/

class mac_reg #(ETH_CHANNELS) extends uvm_reg_block; // ETH_PORT_ID
    `uvm_object_param_utils(net_mod_logic_env::mac_reg#(ETH_CHANNELS))

    rand net_mod_logic_env::mac_control tx_mac_reg[ETH_CHANNELS];
    rand net_mod_logic_env::mac_control rx_mac_reg[ETH_CHANNELS];

    function new(string name = "reg_block");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        for (int i = 0; i < ETH_CHANNELS; i++) begin
            tx_mac_reg[i].set_frontdoor(frontdoor);
            rx_mac_reg[i].set_frontdoor(frontdoor);
        end
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        //Create fields
        for (int unsigned it = 0; it < ETH_CHANNELS; it++) begin
            string it_num;
            it_num.itoa(it);
            //CREATE
            tx_mac_reg[it] = mac_control::type_id::create({"status_", it_num});
            rx_mac_reg[it] = mac_control::type_id::create({"status_", it_num});
            //BUILD and CONFIGURE register
            tx_mac_reg[it].build();
            tx_mac_reg[it].configure(this);
            rx_mac_reg[it].build();
            rx_mac_reg[it].configure(this);
        end

        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        //Add registers to map
        for (int unsigned it = 0; it < ETH_CHANNELS; it++) begin
            this.default_map.add_reg(tx_mac_reg[it], base + 'h8000 + 0 + 'h0  +it*'h400 + 'h20, "RW");
            this.default_map.add_reg(rx_mac_reg[it], base + 'h8000 + 0 + 'h200+it*'h400 + 'h20, "RW");
        end

        this.lock_model();
    endfunction
endclass
