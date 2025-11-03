// regmodel.sv: Register model
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Tomas Hak <xhakto01@vut.cz>

// SPDX-License-Identifier: BSD-3-Clause

class regmodel#(INTERVAL_COUNT) extends uvm_reg_block;
    `uvm_object_param_utils(uvm_rate_limiter::regmodel#(INTERVAL_COUNT))

    uvm_rate_limiter::status_register status;
    uvm_rate_limiter::data_register section;
    uvm_rate_limiter::data_register interval;
    uvm_rate_limiter::data_register count;
    uvm_rate_limiter::data_register frequency;
    uvm_rate_limiter::data_register speed_ptr;
    uvm_rate_limiter::data_register speed;

    function new(string name = "reg_block");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        uvm_reg_frontdoor c_frontdoor;

        $cast(c_frontdoor, frontdoor.clone());
        status.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        section.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        interval.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        count.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        frequency.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        speed_ptr.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        speed.set_frontdoor(c_frontdoor);

    endfunction

    function void build(uvm_reg_addr_t base, int unsigned bus_width);
        status    = status_register::type_id::create("status");
        section   = data_register::type_id::create("section");
        interval  = data_register::type_id::create("interval");
        count     = data_register::type_id::create("count");
        frequency = data_register::type_id::create("frequency");
        speed_ptr = data_register::type_id::create("speed_ptr");
        speed     = data_register::type_id::create("speed");

        status.build();
        section.build("RW", 1000, 1);
        interval.build("RW", 40, 1);
        count.build("RO", INTERVAL_COUNT, 0);
        frequency.build("RO", 200, 0);
        speed_ptr.build("RW", 0, 1);
        speed.build("RW", 62500, 1);

        status.configure(this);
        section.configure(this);
        interval.configure(this);
        count.configure(this);
        frequency.configure(this);
        speed_ptr.configure(this);
        speed.configure(this);

        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);

        this.default_map.add_reg(status,    'h00, "RW");
        this.default_map.add_reg(section,   'h04, "RW");
        this.default_map.add_reg(interval,  'h08, "RW");
        this.default_map.add_reg(count,     'h0C, "RO");
        this.default_map.add_reg(frequency, 'h10, "RO");
        this.default_map.add_reg(speed_ptr, 'h14, "RW");
        this.default_map.add_reg(speed,     'h18, "RW");

        this.lock_model();
    endfunction
endclass;
