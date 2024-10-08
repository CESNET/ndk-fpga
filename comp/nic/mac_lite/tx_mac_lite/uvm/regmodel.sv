//-- regmodel.sv: register model of rx_mac_lite
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class regmodel extends uvm_reg_block;
    `uvm_object_param_utils(uvm_tx_mac_lite::regmodel)


    rand reg_counter   tfcl;       // total received frames counter -> low part
    rand reg_counter   socl;        // sent octets counter -> low part
    rand reg_counter   dfcl;        // discarded frames counterf -> low part
    rand reg_counter   sfcl;      // counter of frames discarded due to buffer overflow -> low part
    rand reg_counter   tfch;       // total received frames counter -> high part
    rand reg_counter   soch;        // correct frames counter -> high part
    rand reg_counter   dfch;        // discarded frames counterf -> high part
    rand reg_counter   sfch;      // counter of frames discarded due to buffer overflow -> high part

    rand reg_enable    enable;      // enable registers
    rand reg_command   command;
    rand reg_status    status;


    function new(string name = "regmodel");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    virtual function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        uvm_reg_frontdoor casted;

        void'($cast(casted, frontdoor.clone()));
        tfcl     .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        socl     .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        dfcl     .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        sfcl    .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        tfch    .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        soch    .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        dfch     .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        sfch     .set_frontdoor(casted);

        void'($cast(casted, frontdoor.clone()));
        enable   .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        command  .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        status   .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        tfcl    = reg_counter  ::type_id::create("tfcl");
        socl    = reg_counter  ::type_id::create("socl");
        dfcl    = reg_counter  ::type_id::create("dfcl");
        sfcl    = reg_counter  ::type_id::create("sfcl");
        tfch    = reg_counter  ::type_id::create("tfch");
        soch    = reg_counter  ::type_id::create("soch");
        dfch    = reg_counter  ::type_id::create("dfch");
        sfch    = reg_counter  ::type_id::create("sfch");
        enable  = reg_enable   ::type_id::create("enable");
        command = reg_command  ::type_id::create("command");
        status  = reg_status   ::type_id::create("status");


        tfcl    .configure(this);
        socl    .configure(this);
        dfcl    .configure(this);
        sfcl    .configure(this);
        tfch    .configure(this);
        soch    .configure(this);
        dfch    .configure(this);
        sfch    .configure(this);
        enable  .configure(this);
        command .configure(this);
        status  .configure(this);



        tfcl   .build();
        socl   .build();
        dfcl   .build();
        sfcl   .build();
        tfch   .build();
        soch   .build();
        dfch   .build();
        sfch   .build();
        enable .build();
        command.build();
        status .build();

        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        //Add registers to map
        this.default_map.add_reg(tfcl    , 'h00, "RO");
        this.default_map.add_reg(socl    , 'h04, "RO");
        this.default_map.add_reg(dfcl    , 'h08, "RO");
        this.default_map.add_reg(sfcl    , 'h0C, "RO");
        this.default_map.add_reg(tfch    , 'h10, "RO");
        this.default_map.add_reg(soch    , 'h14, "RO");
        this.default_map.add_reg(dfch    , 'h18, "RO");
        this.default_map.add_reg(sfch    , 'h1C, "RO");
        this.default_map.add_reg(enable  , 'h20, "RW");
        this.default_map.add_reg(command , 'h2C, "RW");
        this.default_map.add_reg(status  , 'h30, "RO");

        this.lock_model();
    endfunction
endclass


