//-- regmodel.sv: register model of rx_mac_lite
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class base_cnt#(MAC_COUNT) extends uvm_reg_block;
    `uvm_object_param_utils(uvm_rx_mac_lite::base_cnt#(MAC_COUNT))


    rand reg_counter   trfcl;       // total received frames counter -> low part
    rand reg_counter   cfcl;        // correct frames counter -> low part
    rand reg_counter   dfcl;        // discarded frames counterf -> low part
    rand reg_counter   bodfcl;      // counter of frames discarded due to buffer overflow -> low part
    rand reg_counter   trfch;       // total received frames counter -> high part
    rand reg_counter   cfch;        // correct frames counter -> high part
    rand reg_counter   dfch;        // discarded frames counterf -> high part
    rand reg_counter   bodfch;      // counter of frames discarded due to buffer overflow -> high part

    rand reg_enable    enable;      // enable registers
    rand reg_error     error;
    rand reg_status    status;

    rand reg_mtu       min;
    rand reg_mtu       max;
    rand reg_mac_check mac_check;
    rand reg_counter   orocl;       // octets received OK counter -> low  part
    rand reg_counter   oroch;       // octets received OK counter -> high part
    //rand MAC ADDR
    rand reg_mac       mac[MAC_COUNT]; // MAC ADDR


    function new(string name = "base_cnt");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    virtual function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        uvm_reg_frontdoor casted;

        void'($cast(casted, frontdoor.clone()));
        trfcl    .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        cfcl     .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        dfcl     .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        bodfcl   .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        trfch    .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        cfch     .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        dfch     .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        bodfch   .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        enable   .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        error    .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        status   .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        min      .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        max      .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        mac_check.set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        orocl    .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        oroch    .set_frontdoor(casted);
        for (int unsigned it = 0; it < MAC_COUNT; it++) begin
            void'($cast(casted, frontdoor.clone()));
            mac[it].set_frontdoor(casted);
        end
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        trfcl     = reg_counter  ::type_id::create("trfcl");
        cfcl      = reg_counter  ::type_id::create("cfcl");
        dfcl      = reg_counter  ::type_id::create("dfcl");
        bodfcl    = reg_counter  ::type_id::create("bodfcl");
        trfch     = reg_counter  ::type_id::create("trfch");
        cfch      = reg_counter  ::type_id::create("cfch");
        dfch      = reg_counter  ::type_id::create("dfch");
        bodfch    = reg_counter  ::type_id::create("bodfch");
        enable    = reg_enable   ::type_id::create("enable");
        error     = reg_error    ::type_id::create("error");
        status    = reg_status   ::type_id::create("status");
        min       = reg_mtu      ::type_id::create("min");
        max       = reg_mtu      ::type_id::create("max");
        mac_check = reg_mac_check::type_id::create("mac_check");
        orocl     = reg_counter  ::type_id::create("orocl");
        oroch     = reg_counter  ::type_id::create("oroch");

        for (int unsigned it = 0; it < MAC_COUNT; it++) begin
            mac[it] = reg_mac::type_id::create($sformatf("mac_%0d", it));
        end



        trfcl    .configure(this);
        cfcl     .configure(this);
        dfcl     .configure(this);
        bodfcl   .configure(this);
        trfch    .configure(this);
        cfch     .configure(this);
        dfch     .configure(this);
        bodfch   .configure(this);
        enable   .configure(this);
        error    .configure(this);
        status   .configure(this);
        min      .configure(this);
        max      .configure(this);
        mac_check.configure(this);
        orocl    .configure(this);
        oroch    .configure(this);
        for (int unsigned it = 0; it < MAC_COUNT; it++) begin
            mac[it].configure(this);
        end


        trfcl    .build();
        cfcl     .build();
        dfcl     .build();
        bodfcl   .build();
        trfch    .build();
        cfch     .build();
        dfch     .build();
        bodfch   .build();
        enable   .build();
        error    .build();
        status   .build();
        min      .build(64);
        max      .build(1526);
        mac_check.build();
        orocl    .build();
        oroch    .build();
        for (int unsigned it = 0; it < MAC_COUNT; it++) begin
            mac[it].build();
        end

        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        //Add registers to map
        this.default_map.add_reg(trfcl    , 'h00, "RO");
        this.default_map.add_reg(cfcl     , 'h04, "RO");
        this.default_map.add_reg(dfcl     , 'h08, "RO");
        this.default_map.add_reg(bodfcl   , 'h0C, "RO");
        this.default_map.add_reg(trfch    , 'h10, "RO");
        this.default_map.add_reg(cfch     , 'h14, "RO");
        this.default_map.add_reg(dfch     , 'h18, "RO");
        this.default_map.add_reg(bodfch   , 'h1C, "RO");
        this.default_map.add_reg(enable   , 'h20, "RW");
        this.default_map.add_reg(error    , 'h24, "RW");
        this.default_map.add_reg(status   , 'h28, "RW");
        this.default_map.add_reg(min      , 'h30, "RW");
        this.default_map.add_reg(max      , 'h34, "RW");
        this.default_map.add_reg(mac_check, 'h38, "RW");
        this.default_map.add_reg(orocl    , 'h3C, "RO");
        this.default_map.add_reg(oroch    , 'h40, "RO");
        for (int unsigned it = 0; it < MAC_COUNT; it++) begin
            this.default_map.add_reg(mac[it] , 'h80 + it * 'h08, "RW");
        end

        this.lock_model();
    endfunction
endclass


