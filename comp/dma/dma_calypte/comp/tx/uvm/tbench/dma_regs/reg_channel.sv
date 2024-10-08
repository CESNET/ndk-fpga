// reg_channel.sv: Register model for one channel
// Copyright (C) 2022-2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class regmodel_channel extends uvm_reg_block;
    `uvm_object_utils(uvm_tx_dma_calypte_regs::regmodel_channel)

    rand control_register  control_reg;
    rand status_register   status_reg;
    rand pointer_register  sw_data_pointer_reg;
    rand pointer_register  sw_hdr_pointer_reg;
    rand pointer_register  hw_data_pointer_reg;
    rand pointer_register  hw_hdr_pointer_reg;
    rand pointer_mask_register  data_mask_reg;
    rand pointer_mask_register  hdr_mask_reg;
    rand cnt_register      sent_packets_reg;
    rand cnt_register      discarded_packets_reg;
    rand cnt_register      sent_bytes_reg;
    rand cnt_register      discarded_bytes_reg;

    function new(string name = "regmodel_channel");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        uvm_reg_frontdoor c_frontdoor;

        $cast(c_frontdoor, frontdoor.clone());
        control_reg          .set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        status_reg           .set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        sw_data_pointer_reg  .set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        sw_hdr_pointer_reg   .set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        hw_data_pointer_reg  .set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        hw_hdr_pointer_reg   .set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        data_mask_reg        .set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        hdr_mask_reg         .set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        sent_packets_reg     .set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        sent_bytes_reg       .set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        discarded_packets_reg.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        discarded_bytes_reg  .set_frontdoor(c_frontdoor);
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        //CREATE
        control_reg           = control_register     ::type_id::create("control_reg");
        status_reg            = status_register      ::type_id::create("status_reg");
        sw_data_pointer_reg   = pointer_register     ::type_id::create("sw_data_pointer_reg");
        sw_hdr_pointer_reg    = pointer_register     ::type_id::create("sw_hdr_pointer_reg");
        hw_data_pointer_reg   = pointer_register     ::type_id::create("hw_data_pointer_reg");
        hw_hdr_pointer_reg    = pointer_register     ::type_id::create("hw_hdr_pointer_reg");
        data_mask_reg         = pointer_mask_register::type_id::create("data_mask_reg");
        hdr_mask_reg          = pointer_mask_register::type_id::create("hdr_mask_reg");
        sent_packets_reg      = cnt_register         ::type_id::create("sent_packets_reg");
        sent_bytes_reg        = cnt_register         ::type_id::create("sent_bytes_reg");
        discarded_bytes_reg   = cnt_register         ::type_id::create("discarded_bytes_reg");
        discarded_packets_reg = cnt_register         ::type_id::create("discarded_packets_reg");

        //BUILD and CONFIGURE register
        control_reg          .build();
        status_reg           .build();
        sw_data_pointer_reg  .build();
        sw_hdr_pointer_reg   .build();
        hw_data_pointer_reg  .build();
        hw_hdr_pointer_reg   .build();
        data_mask_reg        .build();
        hdr_mask_reg         .build();
        sent_packets_reg     .build();
        discarded_packets_reg.build();
        sent_bytes_reg       .build();
        discarded_bytes_reg  .build();

        control_reg          .configure(this);
        status_reg           .configure(this);
        sw_data_pointer_reg  .configure(this);
        sw_hdr_pointer_reg   .configure(this);
        hw_data_pointer_reg  .configure(this);
        hw_hdr_pointer_reg   .configure(this);
        data_mask_reg        .configure(this);
        hdr_mask_reg         .configure(this);
        sent_packets_reg     .configure(this);
        discarded_packets_reg.configure(this);
        sent_bytes_reg       .configure(this);
        discarded_bytes_reg  .configure(this);

        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);

        //Add registers to map
        this.default_map.add_reg(control_reg,           'h00, "RW");
        this.default_map.add_reg(status_reg,            'h04, "RO");

        this.default_map.add_reg(sw_data_pointer_reg,   'h10, "RW");
        this.default_map.add_reg(sw_hdr_pointer_reg,    'h14, "RW");
        this.default_map.add_reg(hw_data_pointer_reg,   'h18, "RO");
        this.default_map.add_reg(hw_hdr_pointer_reg,    'h1C, "RO");

        this.default_map.add_reg(data_mask_reg,         'h58, "RO");
        this.default_map.add_reg(hdr_mask_reg,          'h5C, "RO");

        this.default_map.add_reg(sent_packets_reg,      'h60, "RW");
        this.default_map.add_reg(sent_bytes_reg,        'h68, "RW");
        this.default_map.add_reg(discarded_packets_reg, 'h70, "RW");
        this.default_map.add_reg(discarded_bytes_reg,   'h78, "RW");

        this.lock_model();
    endfunction
endclass
