// regmodel.sv: Register model for all channels
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class regmodel_top #(int unsigned CHANNELS) extends uvm_reg_block;
    `uvm_object_param_utils(uvm_tx_dma_calypte_regs::regmodel_top #(CHANNELS))

    uvm_tx_dma_calypte_regs::regmodel_channel m_regmodel_channel [CHANNELS];

    function new(string name = "m_regmodel_top");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        uvm_reg_frontdoor c_frontdoor;
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            $cast(c_frontdoor, frontdoor.clone());
            m_regmodel_channel[it].set_frontdoor(c_frontdoor);
        end
    endfunction

    function void build(uvm_reg_addr_t base, int unsigned bus_width);
        //Create fields
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            string it_num;
            it_num.itoa(it);
            //CREATE
            m_regmodel_channel[it] = uvm_tx_dma_calypte_regs::regmodel_channel::type_id::create({"m_regmodel_channel_", it_num}, , get_full_name());
            //BUILD and CONFIGURE register
            m_regmodel_channel[it].build('h0, bus_width);
            m_regmodel_channel[it].configure(this, {"m_regmodel_channel_", it_num});
        end

        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);

        //Add registers to map
        for(int unsigned it = 0; it < CHANNELS; it++) begin
            this.default_map.add_submap(m_regmodel_channel[it].default_map, it * 32'h80);
        end

        this.lock_model();
    endfunction
endclass
