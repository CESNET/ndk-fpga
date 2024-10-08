/*
 * file       : block.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: regmodel for application core
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class regmodel #(INPUT_CHANNELS, OUTPUT_CHANNELS, RESET_TYPE) extends uvm_reg_block;
    `uvm_object_param_utils(uvm_channel_router::regmodel#(INPUT_CHANNELS, OUTPUT_CHANNELS, RESET_TYPE))

    rand reg_dist channel[INPUT_CHANNELS];

    function new(string name = "reg_block");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        for(int unsigned it = 0; it < INPUT_CHANNELS; it++) begin
            uvm_reg_frontdoor casted;

            void'($cast(casted, frontdoor.clone()));
            channel[it].set_frontdoor(casted);
        end
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        //Create fields
        for (int unsigned it = 0; it < INPUT_CHANNELS; it++) begin
            string it_num;
            it_num.itoa(it);
            //CREATE
            channel[it] = reg_dist::type_id::create({"status_", it_num});
            //BUILD and CONFIGURE register
            case (RESET_TYPE)
                0 : channel[it].build('h0, 'h0, 'h0);
                1 : channel[it].build(OUTPUT_CHANNELS-1, 'h0, 'h1);
                2 : channel[it].build(OUTPUT_CHANNELS/INPUT_CHANNELS*(it+1)-1, OUTPUT_CHANNELS/INPUT_CHANNELS*it, 'h1);
                default : `uvm_fatal(this.get_full_name(), "\n\tUnknown reset generic")
            endcase
            channel[it].configure(this);
        end

        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        //Add registers to map
        for(int unsigned it = 0; it < INPUT_CHANNELS; it++) begin
            this.default_map.add_reg(channel[it], it * 'h4, "RW");
        end

        this.lock_model();
    endfunction
endclass

