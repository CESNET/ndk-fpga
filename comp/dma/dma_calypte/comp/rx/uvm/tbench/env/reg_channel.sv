//-- reg_channel.sv: Registre model for one channel
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class reg_channel extends uvm_reg_block;
    `uvm_object_utils(uvm_dma_ll::reg_channel)

    rand uvm_dma_ll::control_register      control;
    rand uvm_dma_ll::status_register       status;
    rand uvm_dma_ll::pointer_register      sw_data_pointer;
    rand uvm_dma_ll::pointer_register      sw_hdr_pointer;
    rand uvm_dma_ll::pointer_register      hw_data_pointer;
    rand uvm_dma_ll::pointer_register      hw_hdr_pointer;
    rand uvm_dma_ll::addr_register         data_base;
    rand uvm_dma_ll::addr_register         hdr_base;
    rand uvm_dma_ll::pointer_register      data_mask;
    rand uvm_dma_ll::pointer_register      hdr_mask;
    rand uvm_dma_ll::cnt_register          sent_packets_cnt;
    rand uvm_dma_ll::cnt_register          sent_bytes_cnt;
    rand uvm_dma_ll::cnt_register          disc_packets_cnt;
    rand uvm_dma_ll::cnt_register          disc_bytes_cnt;

    function new(string name = "reg_block");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        uvm_reg_frontdoor c_frontdoor;
        $cast(c_frontdoor, frontdoor.clone());
        control.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        status.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        sw_data_pointer.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        sw_hdr_pointer.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        hw_data_pointer.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        hw_hdr_pointer.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        data_base.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        hdr_base.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        data_mask.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        hdr_mask.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        sent_packets_cnt.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        sent_bytes_cnt.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        disc_packets_cnt.set_frontdoor(c_frontdoor);
        $cast(c_frontdoor, frontdoor.clone());
        disc_bytes_cnt.set_frontdoor(c_frontdoor);
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        //CREATE
        control = control_register::type_id::create("control");
        status  = status_register::type_id::create("status");
        sw_data_pointer = uvm_dma_ll::pointer_register::type_id::create("sw_data_pointer");
        sw_hdr_pointer  = uvm_dma_ll::pointer_register::type_id::create("sw_hdr_pointer");
        hw_data_pointer = uvm_dma_ll::pointer_register::type_id::create("hw_data_pointer");
        hw_hdr_pointer  = uvm_dma_ll::pointer_register::type_id::create("hw_hdr_pointer");
        data_base = uvm_dma_ll::addr_register::type_id::create("data_base");
        hdr_base  = uvm_dma_ll::addr_register::type_id::create("hdr_base");
        data_mask  = uvm_dma_ll::pointer_register::type_id::create("data_mask");
        hdr_mask   = uvm_dma_ll::pointer_register::type_id::create("hdr_mask");
        sent_packets_cnt = uvm_dma_ll::cnt_register::type_id::create("sent_packets_cnt");
        sent_bytes_cnt   = uvm_dma_ll::cnt_register::type_id::create("sent_bytes_cnt");
        disc_packets_cnt = uvm_dma_ll::cnt_register::type_id::create("disc_packets_cnt");
        disc_bytes_cnt   = uvm_dma_ll::cnt_register::type_id::create("disc_bytes_cnt");
        //BUILD and CONFIGURE register
        control.build();
        status.build();
        sw_data_pointer.build();
        sw_hdr_pointer.build();
        hw_data_pointer.build();
        hw_hdr_pointer.build();
        data_base.build();
        hdr_base.build();
        data_mask.build();
        hdr_mask.build();
        sent_packets_cnt.build();
        sent_bytes_cnt.build();
        disc_packets_cnt.build();
        disc_bytes_cnt.build();

        control.configure(this);
        status.configure(this);
        sw_data_pointer.configure(this);
        sw_hdr_pointer.configure(this);
        hw_data_pointer.configure(this);
        hw_hdr_pointer.configure(this);
        data_base.configure(this);
        hdr_base.configure(this);
        data_mask.configure(this);
        hdr_mask.configure(this);
        sent_packets_cnt.configure(this);
        sent_bytes_cnt.configure(this);
        disc_packets_cnt.configure(this);
        disc_bytes_cnt.configure(this);

        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        //Add registers to map
        this.default_map.add_reg(control          , 'h00, "RW");
        this.default_map.add_reg(status           , 'h04, "RO");
        this.default_map.add_reg(sw_data_pointer  , 'h10, "RW");
        this.default_map.add_reg(sw_hdr_pointer   , 'h14, "RW");
        this.default_map.add_reg(hw_data_pointer  , 'h18, "RO");
        this.default_map.add_reg(hw_hdr_pointer   , 'h1C, "RO");
        this.default_map.add_reg(data_base        , 'h40, "RW");
        this.default_map.add_reg(hdr_base         , 'h48, "RW");
        this.default_map.add_reg(data_mask        , 'h58, "RW");
        this.default_map.add_reg(hdr_mask         , 'h5C, "RW");
        this.default_map.add_reg(sent_packets_cnt , 'h60, "RW");
        this.default_map.add_reg(sent_bytes_cnt   , 'h68, "RW");
        this.default_map.add_reg(disc_packets_cnt , 'h70, "RW");
        this.default_map.add_reg(disc_bytes_cnt   , 'h78, "RW");

        this.lock_model();
    endfunction
endclass
