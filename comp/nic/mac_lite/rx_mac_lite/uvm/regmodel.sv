// regmodel.sv: Register model for RX MAC Lite
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>
//            Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class regmodel #(int unsigned MAC_COUNT) extends uvm_reg_block;
    `uvm_object_param_utils(uvm_rx_mac_lite::regmodel #(MAC_COUNT))

    rand reg_counter trfcl;  // total received frames counter -> low part
    rand reg_counter cfcl;   // correct frames counter -> low part
    rand reg_counter dfcl;   // discarded frames counterf -> low part
    rand reg_counter bodfcl; // counter of frames discarded due to buffer overflow -> low part
    rand reg_counter trfch;  // total received frames counter -> high part
    rand reg_counter cfch;   // correct frames counter -> high part
    rand reg_counter dfch;   // discarded frames counterf -> high part
    rand reg_counter bodfch; // counter of frames discarded due to buffer overflow -> high part

    rand reg_counter disabled_l; // Discarded frames due to RX MAC is disabled | LOW PART
    rand reg_counter disabled_h; //                                            | HIGH PART
    rand reg_counter mac_fltr_l; // Discarded frames due to MAC filter         | LOW PART
    rand reg_counter mac_fltr_h; //                                            | HIGH PART
    rand reg_counter error_l;    // Discarded frames due to error              | LOW PART
    rand reg_counter error_h;    //                                            | HIGH PART
    rand reg_counter err_len_l;  // Discarded frames due to LEN error          | LOW PART
    rand reg_counter err_len_h;  //                                            | HIGH PART
    rand reg_counter err_mii_l;  // Discarded frames due to MII error          | LOW PART
    rand reg_counter err_mii_h;  //                                            | HIGH PART
    rand reg_counter err_crc_l;  // Discarded frames due to CRC error          | LOW PART
    rand reg_counter err_crc_h;  //

    rand reg_enable  enable; // enable registers
    rand reg_error   error;
    rand reg_status  status;
    rand reg_command command;

    rand reg_mtu       min;
    rand reg_mtu       max;
    rand reg_mac_check mac_check;
    rand reg_counter   orocl;       // octets received OK counter -> low  part
    rand reg_counter   oroch;       // octets received OK counter -> high part
    rand reg_mac       mac[MAC_COUNT]; // MAC ADDR

    rand reg_counter crc_err_l;       // total received frames counter -> low part
    rand reg_counter over_mtu_l_addr;
    rand reg_counter below_min_l_addr;
    rand reg_counter bcast_frames_l_addr;
    rand reg_counter mcast_frames_l_addr;
    rand reg_counter fragment_frames_l_addr;
    rand reg_counter jabber_frames_l_addr;
    rand reg_counter trans_octets_l_addr;
    rand reg_counter crc_err_h;       // total received frames counter -> low part
    rand reg_counter over_mtu_h_addr;
    rand reg_counter below_min_h_addr;
    rand reg_counter bcast_frames_h_addr;
    rand reg_counter mcast_frames_h_addr;
    rand reg_counter fragment_frames_h_addr;
    rand reg_counter jabber_frames_h_addr;
    rand reg_counter trans_octets_h_addr;

    rand reg_counter frames_undersize_l; // LOW PART
    rand reg_counter frames_undersize_h; // HIGH PART
    rand reg_counter frames_64_l;        // LOW PART
    rand reg_counter frames_64_h;        // HIGH PART
    rand reg_counter frames_65_127_l;    // LOW PART
    rand reg_counter frames_65_127_h;    // HIGH PART
    rand reg_counter frames_128_255_l;   // LOW PART
    rand reg_counter frames_128_255_h;   // HIGH PART
    rand reg_counter frames_256_511_l;   // LOW PART
    rand reg_counter frames_256_511_h;   // HIGH PART
    rand reg_counter frames_512_1023_l;  // LOW PART
    rand reg_counter frames_512_1023_h;  // HIGH PART
    rand reg_counter frames_1024_1518_l; // LOW PART
    rand reg_counter frames_1024_1518_h; // HIGH PART
    rand reg_counter frames_over_1518_l; // LOW PART
    rand reg_counter frames_over_1518_h; // HIGH PART
    rand reg_counter frames_1519_2047_l; // LOW PART
    rand reg_counter frames_1519_2047_h; // HIGH PART
    rand reg_counter frames_2048_4095_l; // LOW PART
    rand reg_counter frames_2048_4095_h; // HIGH PART
    rand reg_counter frames_4096_8191_l; // LOW PART
    rand reg_counter frames_4096_8191_h; // HIGH PART
    rand reg_counter frames_over_8191_l; // LOW PART
    rand reg_counter frames_over_8191_h; // HIGH PART

    function new(string name = "regmodel");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    virtual function void set_frontdoor(uvm_reg_frontdoor frontdoor);
        uvm_reg_frontdoor dummy;

        assert($cast(dummy, frontdoor.clone()));
        trfcl    .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        cfcl     .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        dfcl     .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        bodfcl   .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        trfch    .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        cfch     .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        dfch     .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        bodfch   .set_frontdoor(dummy);

        assert($cast(dummy, frontdoor.clone()));
        disabled_l.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        disabled_h.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        mac_fltr_l.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        mac_fltr_h.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        error_l   .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        error_h   .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        err_len_l .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        err_len_h .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        err_mii_l .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        err_mii_h .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        err_crc_l .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        err_crc_h .set_frontdoor(dummy);

        assert($cast(dummy, frontdoor.clone()));
        enable   .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        error    .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        status   .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        command  .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        min      .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        max      .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        mac_check.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        orocl    .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        oroch    .set_frontdoor(dummy);

        for (int unsigned it = 0; it < MAC_COUNT; it++) begin
            assert($cast(dummy, frontdoor.clone()));
            mac[it].set_frontdoor(dummy);
        end

        assert($cast(dummy, frontdoor.clone()));
        crc_err_l             .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        over_mtu_l_addr       .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        below_min_l_addr      .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        bcast_frames_l_addr   .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        mcast_frames_l_addr   .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        fragment_frames_l_addr.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        jabber_frames_l_addr  .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        trans_octets_l_addr   .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        crc_err_h             .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        over_mtu_h_addr       .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        below_min_h_addr      .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        bcast_frames_h_addr   .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        mcast_frames_h_addr   .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        fragment_frames_h_addr.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        jabber_frames_h_addr  .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        trans_octets_h_addr   .set_frontdoor(dummy);

        assert($cast(dummy, frontdoor.clone()));
        frames_undersize_l.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_undersize_h.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_64_l       .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_64_h       .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_65_127_l   .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_65_127_h   .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_128_255_l  .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_128_255_h  .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_256_511_l  .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_256_511_h  .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_512_1023_l .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_512_1023_h .set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_1024_1518_l.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_1024_1518_h.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_over_1518_l.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_over_1518_h.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_1519_2047_l.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_1519_2047_h.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_2048_4095_l.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_2048_4095_h.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_4096_8191_l.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_4096_8191_h.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_over_8191_l.set_frontdoor(dummy);
        assert($cast(dummy, frontdoor.clone()));
        frames_over_8191_h.set_frontdoor(dummy);
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        // -------- //
        // Creating //
        // -------- //

        trfcl  = reg_counter::type_id::create("trfcl");
        cfcl   = reg_counter::type_id::create("cfcl");
        dfcl   = reg_counter::type_id::create("dfcl");
        bodfcl = reg_counter::type_id::create("bodfcl");
        trfch  = reg_counter::type_id::create("trfch");
        cfch   = reg_counter::type_id::create("cfch");
        dfch   = reg_counter::type_id::create("dfch");
        bodfch = reg_counter::type_id::create("bodfch");

        disabled_l = reg_counter::type_id::create("disabled_l");
        disabled_h = reg_counter::type_id::create("disabled_h");
        mac_fltr_l = reg_counter::type_id::create("mac_fltr_l");
        mac_fltr_h = reg_counter::type_id::create("mac_fltr_h");
        error_l    = reg_counter::type_id::create("error_l");
        error_h    = reg_counter::type_id::create("error_h");
        err_len_l  = reg_counter::type_id::create("err_len_l");
        err_len_h  = reg_counter::type_id::create("err_len_h");
        err_mii_l  = reg_counter::type_id::create("err_mii_l");
        err_mii_h  = reg_counter::type_id::create("err_mii_h");
        err_crc_l  = reg_counter::type_id::create("err_crc_l");
        err_crc_h  = reg_counter::type_id::create("err_crc_h");

        enable    = reg_enable   ::type_id::create("enable");
        error     = reg_error    ::type_id::create("error");
        status    = reg_status   ::type_id::create("status");
        command   = reg_command  ::type_id::create("command");
        min       = reg_mtu      ::type_id::create("min");
        max       = reg_mtu      ::type_id::create("max");
        mac_check = reg_mac_check::type_id::create("mac_check");
        orocl     = reg_counter  ::type_id::create("orocl");
        oroch     = reg_counter  ::type_id::create("oroch");

        for (int unsigned it = 0; it < MAC_COUNT; it++) begin
            mac[it] = reg_mac::type_id::create($sformatf("mac_%0d", it));
        end

        crc_err_l              = reg_counter::type_id::create("crc_err_l");
        over_mtu_l_addr        = reg_counter::type_id::create("over_mtu_l_addr");
        below_min_l_addr       = reg_counter::type_id::create("below_min_l_addr");
        bcast_frames_l_addr    = reg_counter::type_id::create("bcast_frames_l_addr");
        mcast_frames_l_addr    = reg_counter::type_id::create("mcast_frames_l_addr");
        fragment_frames_l_addr = reg_counter::type_id::create("fragment_frames_l_addr");
        jabber_frames_l_addr   = reg_counter::type_id::create("jabber_frames_l_addr");
        trans_octets_l_addr    = reg_counter::type_id::create("trans_octets_l_addr");
        crc_err_h              = reg_counter::type_id::create("crc_err_h");
        over_mtu_h_addr        = reg_counter::type_id::create("over_mtu_h_addr");
        below_min_h_addr       = reg_counter::type_id::create("below_min_h_addr");
        bcast_frames_h_addr    = reg_counter::type_id::create("bcast_frames_h_addr");
        mcast_frames_h_addr    = reg_counter::type_id::create("mcast_frames_h_addr");
        fragment_frames_h_addr = reg_counter::type_id::create("fragment_frames_h_addr");
        jabber_frames_h_addr   = reg_counter::type_id::create("jabber_frames_h_addr");
        trans_octets_h_addr    = reg_counter::type_id::create("trans_octets_h_addr");

        frames_undersize_l = reg_counter::type_id::create("frames_undersize_l");
        frames_undersize_h = reg_counter::type_id::create("frames_undersize_h");
        frames_64_l        = reg_counter::type_id::create("frames_64_l");
        frames_64_h        = reg_counter::type_id::create("frames_64_h");
        frames_65_127_l    = reg_counter::type_id::create("frames_65_127_l");
        frames_65_127_h    = reg_counter::type_id::create("frames_65_127_h");
        frames_128_255_l   = reg_counter::type_id::create("frames_128_255_l");
        frames_128_255_h   = reg_counter::type_id::create("frames_128_255_h");
        frames_256_511_l   = reg_counter::type_id::create("frames_256_511_l");
        frames_256_511_h   = reg_counter::type_id::create("frames_256_511_h");
        frames_512_1023_l  = reg_counter::type_id::create("frames_512_1023_l");
        frames_512_1023_h  = reg_counter::type_id::create("frames_512_1023_h");
        frames_1024_1518_l = reg_counter::type_id::create("frames_1024_1518_l");
        frames_1024_1518_h = reg_counter::type_id::create("frames_1024_1518_h");
        frames_over_1518_l = reg_counter::type_id::create("frames_over_1518_l");
        frames_over_1518_h = reg_counter::type_id::create("frames_over_1518_h");
        frames_1519_2047_l = reg_counter::type_id::create("frames_1519_2047_l");
        frames_1519_2047_h = reg_counter::type_id::create("frames_1519_2047_h");
        frames_2048_4095_l = reg_counter::type_id::create("frames_2048_4095_l");
        frames_2048_4095_h = reg_counter::type_id::create("frames_2048_4095_h");
        frames_4096_8191_l = reg_counter::type_id::create("frames_4096_8191_l");
        frames_4096_8191_h = reg_counter::type_id::create("frames_4096_8191_h");
        frames_over_8191_l = reg_counter::type_id::create("frames_over_8191_l");
        frames_over_8191_h = reg_counter::type_id::create("frames_over_8191_h");

        // ----------- //
        // Configuring //
        // ----------- //

        trfcl .configure(this);
        cfcl  .configure(this);
        dfcl  .configure(this);
        bodfcl.configure(this);
        trfch .configure(this);
        cfch  .configure(this);
        dfch  .configure(this);
        bodfch.configure(this);

        disabled_l.configure(this);
        disabled_h.configure(this);
        mac_fltr_l.configure(this);
        mac_fltr_h.configure(this);
        error_l   .configure(this);
        error_h   .configure(this);
        err_len_l .configure(this);
        err_len_h .configure(this);
        err_mii_l .configure(this);
        err_mii_h .configure(this);
        err_crc_l .configure(this);
        err_crc_h .configure(this);

        enable   .configure(this);
        error    .configure(this);
        status   .configure(this);
        command  .configure(this);
        min      .configure(this);
        max      .configure(this);
        mac_check.configure(this);
        orocl    .configure(this);
        oroch    .configure(this);

        for (int unsigned it = 0; it < MAC_COUNT; it++) begin
            mac[it].configure(this);
        end

        crc_err_l             .configure(this);
        over_mtu_l_addr       .configure(this);
        below_min_l_addr      .configure(this);
        bcast_frames_l_addr   .configure(this);
        mcast_frames_l_addr   .configure(this);
        fragment_frames_l_addr.configure(this);
        jabber_frames_l_addr  .configure(this);
        trans_octets_l_addr   .configure(this);
        crc_err_h             .configure(this);
        over_mtu_h_addr       .configure(this);
        below_min_h_addr      .configure(this);
        bcast_frames_h_addr   .configure(this);
        mcast_frames_h_addr   .configure(this);
        fragment_frames_h_addr.configure(this);
        jabber_frames_h_addr  .configure(this);
        trans_octets_h_addr   .configure(this);

        frames_undersize_l.configure(this);
        frames_undersize_h.configure(this);
        frames_64_l       .configure(this);
        frames_64_h       .configure(this);
        frames_65_127_l   .configure(this);
        frames_65_127_h   .configure(this);
        frames_128_255_l  .configure(this);
        frames_128_255_h  .configure(this);
        frames_256_511_l  .configure(this);
        frames_256_511_h  .configure(this);
        frames_512_1023_l .configure(this);
        frames_512_1023_h .configure(this);
        frames_1024_1518_l.configure(this);
        frames_1024_1518_h.configure(this);
        frames_over_1518_l.configure(this);
        frames_over_1518_h.configure(this);
        frames_1519_2047_l.configure(this);
        frames_1519_2047_h.configure(this);
        frames_2048_4095_l.configure(this);
        frames_2048_4095_h.configure(this);
        frames_4096_8191_l.configure(this);
        frames_4096_8191_h.configure(this);
        frames_over_8191_l.configure(this);
        frames_over_8191_h.configure(this);

        // -------- //
        // Building //
        // -------- //

        trfcl    .build();
        cfcl     .build();
        dfcl     .build();
        bodfcl   .build();
        trfch    .build();
        cfch     .build();
        dfch     .build();
        bodfch   .build();

        disabled_l.build();
        disabled_h.build();
        mac_fltr_l.build();
        mac_fltr_h.build();
        error_l   .build();
        error_h   .build();
        err_len_l .build();
        err_len_h .build();
        err_mii_l .build();
        err_mii_h .build();
        err_crc_l .build();
        err_crc_h .build();

        enable   .build();
        error    .build();
        status   .build();
        command  .build();
        min      .build(64);
        max      .build(1526);
        mac_check.build();
        orocl    .build();
        oroch    .build();

        for (int unsigned it = 0; it < MAC_COUNT; it++) begin
            mac[it].build();
        end

        crc_err_l             .build();
        over_mtu_l_addr       .build();
        below_min_l_addr      .build();
        bcast_frames_l_addr   .build();
        mcast_frames_l_addr   .build();
        fragment_frames_l_addr.build();
        jabber_frames_l_addr  .build();
        trans_octets_l_addr   .build();
        crc_err_h             .build();
        over_mtu_h_addr       .build();
        below_min_h_addr      .build();
        bcast_frames_h_addr   .build();
        mcast_frames_h_addr   .build();
        fragment_frames_h_addr.build();
        jabber_frames_h_addr  .build();
        trans_octets_h_addr   .build();

        frames_undersize_l.build();
        frames_undersize_h.build();
        frames_64_l       .build();
        frames_64_h       .build();
        frames_65_127_l   .build();
        frames_65_127_h   .build();
        frames_128_255_l  .build();
        frames_128_255_h  .build();
        frames_256_511_l  .build();
        frames_256_511_h  .build();
        frames_512_1023_l .build();
        frames_512_1023_h .build();
        frames_1024_1518_l.build();
        frames_1024_1518_h.build();
        frames_over_1518_l.build();
        frames_over_1518_h.build();
        frames_1519_2047_l.build();
        frames_1519_2047_h.build();
        frames_2048_4095_l.build();
        frames_2048_4095_h.build();
        frames_4096_8191_l.build();
        frames_4096_8191_h.build();
        frames_over_8191_l.build();
        frames_over_8191_h.build();

        // ------- //
        // Mapping //
        // ------- //

        this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);

        this.default_map.add_reg(trfcl,  'h00, "RO");
        this.default_map.add_reg(cfcl,   'h04, "RO");
        this.default_map.add_reg(dfcl,   'h08, "RO");
        this.default_map.add_reg(bodfcl, 'h0C, "RO");
        this.default_map.add_reg(trfch,  'h10, "RO");
        this.default_map.add_reg(cfch,   'h14, "RO");
        this.default_map.add_reg(dfch,   'h18, "RO");
        this.default_map.add_reg(bodfch, 'h1C, "RO");

        this.default_map.add_reg(disabled_l, 'h1B0, "RO");
        this.default_map.add_reg(disabled_h, 'h1B4, "RO");
        this.default_map.add_reg(mac_fltr_l, 'h1A0, "RO");
        this.default_map.add_reg(mac_fltr_h, 'h1A4, "RO");
        this.default_map.add_reg(error_l,    'h1A8, "RO");
        this.default_map.add_reg(error_h,    'h1AC, "RO");
        this.default_map.add_reg(err_len_l,  'h1C8, "RO");
        this.default_map.add_reg(err_len_h,  'h1CC, "RO");
        this.default_map.add_reg(err_mii_l,  'h1B8, "RO");
        this.default_map.add_reg(err_mii_h,  'h1BC, "RO");
        this.default_map.add_reg(err_crc_l,  'h1C0, "RO");
        this.default_map.add_reg(err_crc_h,  'h1C4, "RO");

        this.default_map.add_reg(enable,    'h20, "RW");
        this.default_map.add_reg(error,     'h24, "RW");
        this.default_map.add_reg(status,    'h28, "RW");
        this.default_map.add_reg(command,   'h2C, "WO");
        this.default_map.add_reg(min,       'h30, "RW");
        this.default_map.add_reg(max,       'h34, "RW");
        this.default_map.add_reg(mac_check, 'h38, "RW");
        this.default_map.add_reg(orocl,     'h3C, "RO");
        this.default_map.add_reg(oroch,     'h40, "RO");

        for (int unsigned it = 0; it < MAC_COUNT; it++) begin
            this.default_map.add_reg(mac[it], 'h80 + it*'h08, "RW");
        end

        this.default_map.add_reg(crc_err_l,              'h100, "RO");
        this.default_map.add_reg(over_mtu_l_addr,        'h104, "RO");
        this.default_map.add_reg(below_min_l_addr,       'h108, "RO");
        this.default_map.add_reg(bcast_frames_l_addr,    'h10C, "RO");
        this.default_map.add_reg(mcast_frames_l_addr,    'h110, "RO");
        this.default_map.add_reg(fragment_frames_l_addr, 'h114, "RO");
        this.default_map.add_reg(jabber_frames_l_addr,   'h118, "RO");
        this.default_map.add_reg(trans_octets_l_addr,    'h11C, "RO");
        this.default_map.add_reg(crc_err_h,              'h138, "RO");
        this.default_map.add_reg(over_mtu_h_addr,        'h13C, "RO");
        this.default_map.add_reg(below_min_h_addr,       'h140, "RO");
        this.default_map.add_reg(bcast_frames_h_addr,    'h144, "RO");
        this.default_map.add_reg(mcast_frames_h_addr,    'h148, "RO");
        this.default_map.add_reg(fragment_frames_h_addr, 'h14C, "RO");
        this.default_map.add_reg(jabber_frames_h_addr,   'h150, "RO");
        this.default_map.add_reg(trans_octets_h_addr,    'h154, "RO");

        this.default_map.add_reg(frames_undersize_l, 'h178, "RO");
        this.default_map.add_reg(frames_undersize_h, 'h17C, "RO");
        this.default_map.add_reg(frames_64_l,        'h120, "RO");
        this.default_map.add_reg(frames_64_h,        'h158, "RO");
        this.default_map.add_reg(frames_65_127_l,    'h124, "RO");
        this.default_map.add_reg(frames_65_127_h,    'h15C, "RO");
        this.default_map.add_reg(frames_128_255_l,   'h128, "RO");
        this.default_map.add_reg(frames_128_255_h,   'h160, "RO");
        this.default_map.add_reg(frames_256_511_l,   'h12C, "RO");
        this.default_map.add_reg(frames_256_511_h,   'h164, "RO");
        this.default_map.add_reg(frames_512_1023_l,  'h130, "RO");
        this.default_map.add_reg(frames_512_1023_h,  'h168, "RO");
        this.default_map.add_reg(frames_1024_1518_l, 'h134, "RO");
        this.default_map.add_reg(frames_1024_1518_h, 'h16C, "RO");
        this.default_map.add_reg(frames_over_1518_l, 'h170, "RO");
        this.default_map.add_reg(frames_over_1518_h, 'h174, "RO");
        this.default_map.add_reg(frames_1519_2047_l, 'h180, "RO");
        this.default_map.add_reg(frames_1519_2047_h, 'h184, "RO");
        this.default_map.add_reg(frames_2048_4095_l, 'h188, "RO");
        this.default_map.add_reg(frames_2048_4095_h, 'h18C, "RO");
        this.default_map.add_reg(frames_4096_8191_l, 'h190, "RO");
        this.default_map.add_reg(frames_4096_8191_h, 'h194, "RO");
        this.default_map.add_reg(frames_over_8191_l, 'h198, "RO");
        this.default_map.add_reg(frames_over_8191_h, 'h19C, "RO");

        this.lock_model();
    endfunction

endclass
