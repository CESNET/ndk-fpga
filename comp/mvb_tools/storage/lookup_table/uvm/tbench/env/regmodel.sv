//-- regmodel.sv: register model
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class regmodel#(REG_DEPTH, SW_WIDTH) extends uvm_reg_block;
    `uvm_object_param_utils(uvm_lookup_table::regmodel#(REG_DEPTH, SW_WIDTH))

    uvm_mem lut;

    function new(string name = "m_regmodel");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        uvm_reg_frontdoor c_front;
        $cast(c_front, frontdoor.clone());
        lut.set_frontdoor(c_front);
    endfunction

    function void build(uvm_reg_addr_t base, int unsigned bus_width);

        // Create MEM
        lut = new("lut", 2**REG_DEPTH, SW_WIDTH);
        lut.configure(this);

        // create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        // Add registers to map
        this.default_map.add_mem(lut, .offset(0), .rights("RW"));

        this.lock_model();
    endfunction
endclass
