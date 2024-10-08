/*
 * file       : regmodel.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: regmodel for application core
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class regmodel #(ETH_STREAMS, CHANNELS, DMA_STREAMS, OUTPUT_CHANNELS) extends uvm_app_core::regmodel;
    `uvm_object_param_utils(uvm_app_core_minimal::regmodel #(ETH_STREAMS, CHANNELS, DMA_STREAMS, OUTPUT_CHANNELS))

    localparam APP_RX_CHANNELS = OUTPUT_CHANNELS/(ETH_STREAMS/DMA_STREAMS);

    rand uvm_channel_router::regmodel #(CHANNELS, APP_RX_CHANNELS, 2) stream[ETH_STREAMS];

    localparam MEM_TESTERS = 2;

    function new(string name = "reg_block");
        super.new(name);
    endfunction

    function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        for(int unsigned it = 0; it < ETH_STREAMS; it++) begin
            stream[it].set_frontdoor(frontdoor);
        end
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        logic [64-1:0] addr_step = 2**(25-$clog2(ETH_STREAMS + MEM_TESTERS));

        //Create fields
        for (int unsigned it = 0; it < ETH_STREAMS; it++) begin
            string it_num;
            it_num.itoa(it);
            //CREATE
            stream[it] = uvm_channel_router::regmodel#(CHANNELS, APP_RX_CHANNELS, 2)::type_id::create({"status_", it_num}, , get_full_name());
            //BUILD and CONFIGURE register
            stream[it].build('h0, bus_width);
            stream[it].configure(this, {"status_", it_num});
        end

        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        //Add registers to map
        for(int unsigned it = 0; it < ETH_STREAMS; it++) begin
            this.default_map.add_submap(stream[it].default_map, it * addr_step);
        end

        this.lock_model();
    endfunction
endclass

