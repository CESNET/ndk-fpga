
//-- regmodel.sv: register model of rx_mac_lite
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class reg2bus_indirect_frontdoor_sync extends uvm_common::sync_id;
    int unsigned bank;

    function new();
        super.new();
        bank = 1;
    endfunction
endclass


class frontdoor_command_cbs extends uvm_mi::base_reg_frontdoor_cbs;
    local reg2bus_indirect_frontdoor_sync sync;
    local int unsigned id;
    local int unsigned offset;

    function new(int unsigned id, reg2bus_indirect_frontdoor_sync sync);
        this.id   = id;
        this.sync = sync;
    endfunction

    virtual task cbs_pre(uvm_reg_frontdoor fr);
        sync.get(id);
    endtask

    virtual task cbs_post(uvm_reg_frontdoor fr);
        int unsigned data;

        if (fr.rw_info.kind == UVM_WRITE) begin
            data = fr.rw_info.value[0];

            if (this.sync.bank == 1) begin
                if (data == 3) begin
                    //switch bank
                    this.sync.bank = 2;
                end
            end else if (this.sync.bank == 2) begin
                if (data == 3) begin
                    //switch bank
                    this.sync.bank = 1;
                end
            end
        end
        sync.put();
    endtask
endclass

class frontdoor_cbs extends uvm_mi::base_reg_frontdoor_cbs;

    local reg2bus_indirect_frontdoor_sync sync;
    local int unsigned id;
    local reg_command command;

    function new(int unsigned id, reg_command  command, reg2bus_indirect_frontdoor_sync sync);
        this.id      = id;
        this.sync    = sync;
        this.command = command;
    endfunction

    virtual task cbs_pre(uvm_reg_frontdoor fr);
        uvm_mi::base_reg_frontdoor c_fr;

        sync.get_start(id);
        while (id != sync.bank) begin
            uvm_mi::base_reg_frontdoor c_fr;

            //uvm_status_e   status;
            //command.write(status, 3);

            $cast(c_fr, fr);
            //c_fr.indirect_switch(offset + 'h2c, 3);
            c_fr.indirect_switch(command.get_address(), 3);
            sync.bank = id;
        end
        sync.get_end();
    endtask

    virtual task cbs_post(uvm_reg_frontdoor fr);
        sync.put();
    endtask

endclass


class regmodel#(MAC_COUNT) extends uvm_reg_block;
    `uvm_object_utils(uvm_rx_mac_lite::regmodel#(MAC_COUNT))

    protected reg2bus_indirect_frontdoor_sync sync;

    rand reg_command   command;
    base_cnt#(MAC_COUNT) base;
    rfc_cnt              rfc;

    function new(string name = "regmodel");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    virtual function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        //reg2bus_indirect_frontdoor new_frontdoor;
        uvm_mi::base_reg_frontdoor new_frontdoor;
        frontdoor_cbs         cbs;
        frontdoor_command_cbs cbs_cmd;

        sync = new();

        if($cast(new_frontdoor, frontdoor.clone()) != 1) begin
            `uvm_fatal(this.get_name(), "\n\tWrong front door seqeuence type!!");
        end
        cbs_cmd = new(0, sync);
        new_frontdoor.register_cbs(cbs_cmd);
        command  .set_frontdoor(new_frontdoor);

        if($cast(new_frontdoor, frontdoor.clone()) != 1) begin
            `uvm_fatal(this.get_name(), "\n\tWrong front door seqeuence type!!");
        end
        cbs = new(1, command, sync);
        new_frontdoor.register_cbs(cbs);
        base.set_frontdoor(new_frontdoor);

        if($cast(new_frontdoor, frontdoor.clone()) != 1) begin
            `uvm_fatal(this.get_name(), "\n\tWrong front door seqeuence type!!");
        end
        cbs = new(2, command, sync);
        new_frontdoor.register_cbs(cbs);
        rfc.set_frontdoor(new_frontdoor);
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        this.command   = reg_command  ::type_id::create("command");
        this.base = base_cnt#(MAC_COUNT)::type_id::create("base", , get_full_name());
        this.rfc  = rfc_cnt::type_id::create("rfc", , get_full_name());

        this.command.configure(this);
        this.base.configure(this);
        this.rfc.configure(this);

        this.command  .build();
        this.base.build(base, bus_width);
        this.rfc.build(base, bus_width);


        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        //Add registers to map
        this.default_map.add_submap(this.base.default_map, 'h0);
        this.default_map.add_submap(this.rfc.default_map, 'h0);
        this.default_map.add_reg(command  , 'h2C, "WO");
        //this.default_map.add_reg(trfcl    , 'h00, "RO");

        this.lock_model();
    endfunction
endclass


