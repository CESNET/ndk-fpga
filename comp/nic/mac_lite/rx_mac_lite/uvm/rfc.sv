//-- regmodel.sv: register model of rx_mac_lite
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class rfc_cnt extends uvm_reg_block;
    `uvm_object_utils(uvm_rx_mac_lite::rfc_cnt)


    rand reg_counter crc_err_l;       // total received frames counter -> low part
    rand reg_counter over_mtu_l_addr;
    rand reg_counter below_min_l_addr;
    rand reg_counter bcast_frames_l_addr;
    rand reg_counter mcast_frames_l_addr;
    rand reg_counter fragment_frames_l_addr;
    rand reg_counter jabber_frames_l_addr;
    rand reg_counter trans_octets_l_addr;
    rand reg_counter frames_64_l_addr;
    rand reg_counter frames_65_127_l_addr;
    rand reg_counter frames_128_255_l_addr;
    rand reg_counter frames_256_511_l_addr;
    rand reg_counter frames_512_1023_l_addr;
    rand reg_counter frames_1024_1518_l_addr;
    rand reg_counter crc_err_h;       // total received frames counter -> low part
    rand reg_counter over_mtu_h_addr;
    rand reg_counter below_min_h_addr;
    rand reg_counter bcast_frames_h_addr;
    rand reg_counter mcast_frames_h_addr;
    rand reg_counter fragment_frames_h_addr;
    rand reg_counter jabber_frames_h_addr;
    rand reg_counter trans_octets_h_addr;
    rand reg_counter frames_64_h_addr;
    rand reg_counter frames_65_127_h_addr;
    rand reg_counter frames_128_255_h_addr;
    rand reg_counter frames_256_511_h_addr;
    rand reg_counter frames_512_1023_h_addr;
    rand reg_counter frames_1024_1518_h_addr;
    rand reg_counter frames_over_1518_l_addr;
    rand reg_counter frames_over_1518_h_addr;
    rand reg_counter frames_below_64_l_addr;
    rand reg_counter frames_below_64_h_addr;

    function new(string name = "regmodel");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    virtual function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        uvm_reg_frontdoor casted;

        void'($cast(casted, frontdoor.clone()));
        crc_err_l              .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        over_mtu_l_addr        .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        below_min_l_addr       .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        bcast_frames_l_addr    .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        mcast_frames_l_addr    .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        fragment_frames_l_addr .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        jabber_frames_l_addr   .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        trans_octets_l_addr    .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_64_l_addr       .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_65_127_l_addr   .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_128_255_l_addr  .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_256_511_l_addr  .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_512_1023_l_addr .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_1024_1518_l_addr.set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        crc_err_h              .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        over_mtu_h_addr        .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        below_min_h_addr       .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        bcast_frames_h_addr    .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        mcast_frames_h_addr    .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        fragment_frames_h_addr .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        jabber_frames_h_addr   .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        trans_octets_h_addr    .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_64_h_addr       .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_65_127_h_addr   .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_128_255_h_addr  .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_256_511_h_addr  .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_512_1023_h_addr .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_1024_1518_h_addr.set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_over_1518_l_addr.set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_over_1518_h_addr.set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_below_64_l_addr .set_frontdoor(casted);
        void'($cast(casted, frontdoor.clone()));
        frames_below_64_h_addr .set_frontdoor(casted);
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        crc_err_l               = reg_counter  ::type_id::create("crc_err_l");
        over_mtu_l_addr         = reg_counter  ::type_id::create("over_mtu_l_addr");
        below_min_l_addr        = reg_counter  ::type_id::create("below_min_l_addr");
        bcast_frames_l_addr     = reg_counter  ::type_id::create("bcast_frames_l_addr");
        mcast_frames_l_addr     = reg_counter  ::type_id::create("mcast_frames_l_addr");
        fragment_frames_l_addr  = reg_counter  ::type_id::create("fragment_frames_l_addr");
        jabber_frames_l_addr    = reg_counter  ::type_id::create("jabber_frames_l_addr");
        trans_octets_l_addr     = reg_counter  ::type_id::create("trans_octets_l_addr");
        frames_64_l_addr        = reg_counter  ::type_id::create("frames_64_l_addr");
        frames_65_127_l_addr    = reg_counter  ::type_id::create("frames_65_127_l_addr");
        frames_128_255_l_addr   = reg_counter  ::type_id::create("frames_128_255_l_addr");
        frames_256_511_l_addr   = reg_counter  ::type_id::create("frames_256_511_l_addr");
        frames_512_1023_l_addr  = reg_counter  ::type_id::create("frames_512_1023_l_addr");
        frames_1024_1518_l_addr = reg_counter  ::type_id::create("frames_1024_1518_l_addr");
        crc_err_h               = reg_counter  ::type_id::create("crc_err_h");
        over_mtu_h_addr         = reg_counter  ::type_id::create("over_mtu_h_addr");
        below_min_h_addr        = reg_counter  ::type_id::create("below_min_h_addr");
        bcast_frames_h_addr     = reg_counter  ::type_id::create("bcast_frames_h_addr");
        mcast_frames_h_addr     = reg_counter  ::type_id::create("mcast_frames_h_addr");
        fragment_frames_h_addr  = reg_counter  ::type_id::create("fragment_frames_h_addr");
        jabber_frames_h_addr    = reg_counter  ::type_id::create("jabber_frames_h_addr");
        trans_octets_h_addr     = reg_counter  ::type_id::create("trans_octets_h_addr");
        frames_64_h_addr        = reg_counter  ::type_id::create("frames_64_h_addr");
        frames_65_127_h_addr    = reg_counter  ::type_id::create("frames_65_127_h_addr");
        frames_128_255_h_addr   = reg_counter  ::type_id::create("frames_128_255_h_addr");
        frames_256_511_h_addr   = reg_counter  ::type_id::create("frames_256_511_h_addr");
        frames_512_1023_h_addr  = reg_counter  ::type_id::create("frames_512_1023_h_addr");
        frames_1024_1518_h_addr = reg_counter  ::type_id::create("frames_1024_1518_h_addr");
        frames_over_1518_l_addr = reg_counter  ::type_id::create("frames_over_1518_l_addr");
        frames_over_1518_h_addr = reg_counter  ::type_id::create("frames_over_1518_h_addr");
        frames_below_64_l_addr  = reg_counter  ::type_id::create("frames_below_64_l_addr");
        frames_below_64_h_addr  = reg_counter  ::type_id::create("frames_below_64_h_addr");

        crc_err_l              .configure(this);
        over_mtu_l_addr        .configure(this);
        below_min_l_addr       .configure(this);
        bcast_frames_l_addr    .configure(this);
        mcast_frames_l_addr    .configure(this);
        fragment_frames_l_addr .configure(this);
        jabber_frames_l_addr   .configure(this);
        trans_octets_l_addr    .configure(this);
        frames_64_l_addr       .configure(this);
        frames_65_127_l_addr   .configure(this);
        frames_128_255_l_addr  .configure(this);
        frames_256_511_l_addr  .configure(this);
        frames_512_1023_l_addr .configure(this);
        frames_1024_1518_l_addr.configure(this);
        crc_err_h              .configure(this);
        over_mtu_h_addr        .configure(this);
        below_min_h_addr       .configure(this);
        bcast_frames_h_addr    .configure(this);
        mcast_frames_h_addr    .configure(this);
        fragment_frames_h_addr .configure(this);
        jabber_frames_h_addr   .configure(this);
        trans_octets_h_addr    .configure(this);
        frames_64_h_addr       .configure(this);
        frames_65_127_h_addr   .configure(this);
        frames_128_255_h_addr  .configure(this);
        frames_256_511_h_addr  .configure(this);
        frames_512_1023_h_addr .configure(this);
        frames_1024_1518_h_addr.configure(this);
        frames_over_1518_l_addr.configure(this);
        frames_over_1518_h_addr.configure(this);
        frames_below_64_l_addr .configure(this);
        frames_below_64_h_addr .configure(this);

        crc_err_l              .build();
        over_mtu_l_addr        .build();
        below_min_l_addr       .build();
        bcast_frames_l_addr    .build();
        mcast_frames_l_addr    .build();
        fragment_frames_l_addr .build();
        jabber_frames_l_addr   .build();
        trans_octets_l_addr    .build();
        frames_64_l_addr       .build();
        frames_65_127_l_addr   .build();
        frames_128_255_l_addr  .build();
        frames_256_511_l_addr  .build();
        frames_512_1023_l_addr .build();
        frames_1024_1518_l_addr.build();
        crc_err_h              .build();
        over_mtu_h_addr        .build();
        below_min_h_addr       .build();
        bcast_frames_h_addr    .build();
        mcast_frames_h_addr    .build();
        fragment_frames_h_addr .build();
        jabber_frames_h_addr   .build();
        trans_octets_h_addr    .build();
        frames_64_h_addr       .build();
        frames_65_127_h_addr   .build();
        frames_128_255_h_addr  .build();
        frames_256_511_h_addr  .build();
        frames_512_1023_h_addr .build();
        frames_1024_1518_h_addr.build();
        frames_over_1518_l_addr.build();
        frames_over_1518_h_addr.build();
        frames_below_64_l_addr .build();
        frames_below_64_h_addr .build();

        //create map
        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        //Add registers to map
        this.default_map.add_reg(crc_err_l               , 'h00, "RO");
        this.default_map.add_reg(over_mtu_l_addr         , 'h04, "RO");
        this.default_map.add_reg(below_min_l_addr        , 'h08, "RO");
        this.default_map.add_reg(bcast_frames_l_addr     , 'h0C, "RO");
        this.default_map.add_reg(mcast_frames_l_addr     , 'h10, "RO");
        this.default_map.add_reg(fragment_frames_l_addr  , 'h14, "RO");
        this.default_map.add_reg(jabber_frames_l_addr    , 'h18, "RO");
        this.default_map.add_reg(trans_octets_l_addr     , 'h1C, "RO");
        this.default_map.add_reg(frames_64_l_addr        , 'h20, "RO");
        this.default_map.add_reg(frames_65_127_l_addr    , 'h24, "RO");
        this.default_map.add_reg(frames_128_255_l_addr   , 'h28, "RO");
        this.default_map.add_reg(frames_256_511_l_addr   , 'h2C, "RO");
        this.default_map.add_reg(frames_512_1023_l_addr  , 'h30, "RO");
        this.default_map.add_reg(frames_1024_1518_l_addr , 'h34, "RO");
        this.default_map.add_reg(crc_err_h               , 'h38, "RO");
        this.default_map.add_reg(over_mtu_h_addr         , 'h3C, "RO");
        this.default_map.add_reg(below_min_h_addr        , 'h40, "RO");
        this.default_map.add_reg(bcast_frames_h_addr     , 'h44, "RO");
        this.default_map.add_reg(mcast_frames_h_addr     , 'h48, "RO");
        this.default_map.add_reg(fragment_frames_h_addr  , 'h4C, "RO");
        this.default_map.add_reg(jabber_frames_h_addr    , 'h50, "RO");
        this.default_map.add_reg(trans_octets_h_addr     , 'h54, "RO");
        this.default_map.add_reg(frames_64_h_addr        , 'h58, "RO");
        this.default_map.add_reg(frames_65_127_h_addr    , 'h5C, "RO");
        this.default_map.add_reg(frames_128_255_h_addr   , 'h60, "RO");
        this.default_map.add_reg(frames_256_511_h_addr   , 'h64, "RO");
        this.default_map.add_reg(frames_512_1023_h_addr  , 'h68, "RO");
        this.default_map.add_reg(frames_1024_1518_h_addr , 'h6C, "RO");
        this.default_map.add_reg(frames_over_1518_l_addr , 'h70, "RO");
        this.default_map.add_reg(frames_over_1518_h_addr , 'h74, "RO");
        this.default_map.add_reg(frames_below_64_l_addr  , 'h78, "RO");
        this.default_map.add_reg(frames_below_64_h_addr  , 'h7C, "RO");

        this.lock_model();
    endfunction
endclass


