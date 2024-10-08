//-- regmodel.sv: register model
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class regmodel#(CHANNELS) extends uvm_reg_block;
    `uvm_object_param_utils(uvm_dma_ll::regmodel#(CHANNELS))


    uvm_dma_ll::reg_channel channel[CHANNELS];


    function new(string name = "m_regmodel");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        uvm_reg_frontdoor c_frontdoor;
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            $cast(c_frontdoor, frontdoor.clone());
            channel[it].set_frontdoor(c_frontdoor);
        end
    endfunction

    function void build(uvm_reg_addr_t base, int unsigned bus_width);
        //Create fields
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            string it_num;
            it_num.itoa(it);
            //CREATE
            channel[it] = uvm_dma_ll::reg_channel::type_id::create({"channel_", it_num}, , get_full_name());
            //BUILD and CONFIGURE register
            channel[it].build('h0, bus_width);
            channel[it].configure(this, {"channel_", it_num});
        end

        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        //Add registers to map
        for(int unsigned it = 0; it < CHANNELS; it++) begin
            this.default_map.add_submap(channel[it].default_map, it * 32'h80);
        end

        this.lock_model();
    endfunction
endclass
