// regmodel.sv: register model
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kříž <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class regmodel #(QUEUES) extends uvm_reg_block;
    `uvm_object_param_utils(uvm_timestamp_limiter::regmodel #(QUEUES))

    uvm_timestamp_limiter::reg_reset_queue         m_rst_q;
    uvm_timestamp_limiter::reg_sel_queue #(QUEUES) m_sel_q;

    function new(string name = "m_regmodel");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        uvm_reg_frontdoor c_frontdoor;
        $cast(c_frontdoor, frontdoor.clone());
        m_rst_q.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        m_sel_q.set_frontdoor(c_frontdoor);
    endfunction

    function void build(uvm_reg_addr_t base, int unsigned bus_width);
        //CREATE
        m_rst_q = uvm_timestamp_limiter::reg_reset_queue::type_id::create("m_rst_q", , get_full_name());
        m_sel_q = uvm_timestamp_limiter::reg_sel_queue #(QUEUES)::type_id::create("m_sel_q", , get_full_name());
        //BUILD and CONFIGURE register
        m_rst_q.build();
        m_sel_q.build();
        m_rst_q.configure(this);
        m_sel_q.configure(this);

        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        //Add registers to map
        this.default_map.add_reg(m_rst_q, 'h00, "WO");
        this.default_map.add_reg(m_sel_q, 'h04, "RW");

        this.lock_model();
    endfunction
endclass
