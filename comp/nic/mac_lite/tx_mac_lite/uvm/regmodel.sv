//-- regmodel.sv: register model of rx_mac_lite
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class regmodel extends uvm_reg_block;
    `uvm_object_utils(uvm_tx_mac_lite::regmodel)

    rand reg_counter tfcl;  // Total received frames | LOW PART
    rand reg_counter tfch;  //                       | HIGH PART
    rand reg_counter tocl;  // Total received octets | LOW PART
    rand reg_counter toch;  //                       | HIGH PART
    rand reg_counter sfcl;  // Sent frames           | LOW PART
    rand reg_counter sfch;  //                       | HIGH PART
    rand reg_counter socl;  // Sent octets           | LOW PART
    rand reg_counter soch;  //                       | HIGH PART
    rand reg_counter dfcl;  // Discarded frames      | LOW PART
    rand reg_counter dfch;  //                       | HIGH PART
    rand reg_counter liecl; // Link error frames     | LOW PART
    rand reg_counter liech; //                       | HIGH PART
    rand reg_counter lnecl; // Length error frames   | LOW PART
    rand reg_counter lnech; //                       | HIGH PART

    rand reg_enable  enable;
    rand reg_command command;
    rand reg_status  status;

    function new(string name = "regmodel");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    virtual function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        uvm_reg_frontdoor casted;

        void'($cast(casted, frontdoor.clone()));
        tfcl .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        tfch .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        tocl .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        toch .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        sfcl .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        sfch .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        socl .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        soch .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        dfcl .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        dfch .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        liecl.set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        liech.set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        lnecl.set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        lnech.set_frontdoor(casted);

        void'($cast(casted, frontdoor.clone()));
        enable .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        command.set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        status .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        // -------- //
        // Creating //
        // -------- //

        tfcl  = reg_counter::type_id::create("tfcl");
        tfch  = reg_counter::type_id::create("tfch");
        tocl  = reg_counter::type_id::create("tocl");
        toch  = reg_counter::type_id::create("toch");
        sfcl  = reg_counter::type_id::create("sfcl");
        sfch  = reg_counter::type_id::create("sfch");
        socl  = reg_counter::type_id::create("socl");
        soch  = reg_counter::type_id::create("soch");
        dfcl  = reg_counter::type_id::create("dfcl");
        dfch  = reg_counter::type_id::create("dfch");
        liecl = reg_counter::type_id::create("liecl");
        liech = reg_counter::type_id::create("liech");
        lnecl = reg_counter::type_id::create("lnecl");
        lnech = reg_counter::type_id::create("lnech");

        enable  = reg_enable ::type_id::create("enable");
        command = reg_command::type_id::create("command");
        status  = reg_status ::type_id::create("status");

        // ----------- //
        // Configuring //
        // ----------- //

        tfcl .configure(this);
        tfch .configure(this);
        tocl .configure(this);
        toch .configure(this);
        sfcl .configure(this);
        sfch .configure(this);
        socl .configure(this);
        soch .configure(this);
        dfcl .configure(this);
        dfch .configure(this);
        liecl.configure(this);
        liech.configure(this);
        lnecl.configure(this);
        lnech.configure(this);

        enable .configure(this);
        command.configure(this);
        status .configure(this);

        // -------- //
        // Building //
        // -------- //

        tfcl .build();
        tfch .build();
        tocl .build();
        toch .build();
        sfcl .build();
        sfch .build();
        socl .build();
        soch .build();
        dfcl .build();
        dfch .build();
        liecl.build();
        liech.build();
        lnecl.build();
        lnech.build();

        enable .build();
        command.build();
        status .build();

        // ------- //
        // Mapping //
        // ------- //

        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);

        this.default_map.add_reg(tfcl , 'h00, "RO");
        this.default_map.add_reg(tfch , 'h10, "RO");
        this.default_map.add_reg(tocl , 'h40, "RO");
        this.default_map.add_reg(toch , 'h44, "RO");
        this.default_map.add_reg(sfcl , 'h0C, "RO");
        this.default_map.add_reg(sfch , 'h1C, "RO");
        this.default_map.add_reg(socl , 'h04, "RO");
        this.default_map.add_reg(soch , 'h14, "RO");
        this.default_map.add_reg(dfcl , 'h08, "RO");
        this.default_map.add_reg(dfch , 'h18, "RO");
        this.default_map.add_reg(liecl, 'h48, "RO");
        this.default_map.add_reg(liech, 'h4C, "RO");
        this.default_map.add_reg(lnecl, 'h50, "RO");
        this.default_map.add_reg(lnech, 'h54, "RO");

        this.default_map.add_reg(enable , 'h20, "RW");
        this.default_map.add_reg(command, 'h2C, "RW");
        this.default_map.add_reg(status , 'h30, "RO");

        this.lock_model();
    endfunction

endclass
