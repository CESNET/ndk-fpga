//-- reg_sequnece.sv: Virtual sequence
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

class read_rx_counters#(RX_MAC_COUNT) extends uvm_sequence;
    `uvm_object_param_utils(uvm_network_mod_env::read_rx_counters#(RX_MAC_COUNT))

    uvm_rx_mac_lite::regmodel#(RX_MAC_COUNT) regmodel;

    typedef enum bit [8-1 : 0]
    {
        SAMPLE = 'h1,
        RESET  = 'h2
    } command_e;

    // ---- //
    // BASE //
    // ---- //

    longint unsigned trfc;
    longint unsigned cfc;
    longint unsigned dfc;
    longint unsigned bodfc;
    longint unsigned oroc;
    longint unsigned disabled;
    longint unsigned mac_fltr;
    longint unsigned error;
    longint unsigned err_len;
    longint unsigned err_mii;
    longint unsigned err_crc;

    // --- //
    // RFC //
    // --- //

    longint unsigned crc_err;
    longint unsigned over_mtu;
    longint unsigned below_min;
    longint unsigned bcast_frames;
    longint unsigned mcast_frames;
    longint unsigned fragment_frames;
    longint unsigned jabber_frames;
    longint unsigned trans_octets;

    // ---- //
    // HIST //
    // ---- //

    longint unsigned frames_undersize;
    longint unsigned frames_64;
    longint unsigned frames_65_127;
    longint unsigned frames_128_255;
    longint unsigned frames_256_511;
    longint unsigned frames_512_1023;
    longint unsigned frames_1024_1518;
    longint unsigned frames_over_1518;
    longint unsigned frames_1519_2047;
    longint unsigned frames_2048_4095;
    longint unsigned frames_4096_8191;
    longint unsigned frames_over_8191;

    function new(string name = "read_rx_counters");
        super.new(name);
    endfunction

    virtual task send_command(command_e command);
        uvm_status_e status;
        regmodel.command.write(status, command);
    endtask

    virtual task read_counter(uvm_reg reg_counter_l, uvm_reg reg_counter_h, output longint unsigned output_value);
        uvm_status_e   status;
        uvm_reg_data_t data;
        reg_counter_l.read(status, data);
        output_value[32-1 : 0] = data;
        reg_counter_h.read(status, data);
        output_value[64-1 : 32] = data;
    endtask

    virtual task reset();
        send_command(RESET);
    endtask

    virtual task body();
        send_command(SAMPLE);

        #(30ns);

        fork
            // ---- //
            // BASE //
            // ---- //

            read_counter(regmodel.trfcl,  regmodel.trfch,  trfc);
            read_counter(regmodel.cfcl,   regmodel.cfch,   cfc);
            read_counter(regmodel.dfcl,   regmodel.dfch,   dfc);
            read_counter(regmodel.bodfcl, regmodel.bodfch, bodfc);
            read_counter(regmodel.orocl,  regmodel.oroch,  oroc);

            // --- //
            // RFC //
            // --- //

            read_counter(regmodel.crc_err_l,              regmodel.crc_err_h,              crc_err);
            read_counter(regmodel.over_mtu_l_addr,        regmodel.over_mtu_h_addr,        over_mtu);
            read_counter(regmodel.below_min_l_addr,       regmodel.below_min_h_addr,       below_min);
            read_counter(regmodel.bcast_frames_l_addr,    regmodel.bcast_frames_h_addr,    bcast_frames);
            read_counter(regmodel.mcast_frames_l_addr,    regmodel.mcast_frames_h_addr,    mcast_frames);
            read_counter(regmodel.fragment_frames_l_addr, regmodel.fragment_frames_h_addr, fragment_frames);
            read_counter(regmodel.jabber_frames_l_addr,   regmodel.jabber_frames_h_addr,   jabber_frames);
            read_counter(regmodel.trans_octets_l_addr,    regmodel.trans_octets_h_addr,    trans_octets);

            // ---- //
            // HIST //
            // ---- //

            read_counter(regmodel.frames_undersize_l, regmodel.frames_undersize_h, frames_undersize);
            read_counter(regmodel.frames_64_l,        regmodel.frames_64_h,        frames_64);
            read_counter(regmodel.frames_65_127_l,    regmodel.frames_65_127_h,    frames_65_127);
            read_counter(regmodel.frames_128_255_l,   regmodel.frames_128_255_h,   frames_128_255);
            read_counter(regmodel.frames_256_511_l,   regmodel.frames_256_511_h,   frames_256_511);
            read_counter(regmodel.frames_512_1023_l,  regmodel.frames_512_1023_h,  frames_512_1023);
            read_counter(regmodel.frames_1024_1518_l, regmodel.frames_1024_1518_h, frames_1024_1518);
            read_counter(regmodel.frames_over_1518_l, regmodel.frames_over_1518_h, frames_over_1518);
            read_counter(regmodel.frames_1519_2047_l, regmodel.frames_1519_2047_h, frames_1519_2047);
            read_counter(regmodel.frames_2048_4095_l, regmodel.frames_2048_4095_h, frames_2048_4095);
            read_counter(regmodel.frames_4096_8191_l, regmodel.frames_4096_8191_h, frames_4096_8191);
            read_counter(regmodel.frames_over_8191_l, regmodel.frames_over_8191_h, frames_over_8191);
        join
    endtask

    virtual function bit zero();
        return (
            // BASE
            trfc  == 0 &&
            cfc   == 0 &&
            dfc   == 0 &&
            bodfc == 0 &&
            oroc  == 0 &&
            // RFC
            crc_err         == 0 &&
            over_mtu        == 0 &&
            below_min       == 0 &&
            bcast_frames    == 0 &&
            mcast_frames    == 0 &&
            fragment_frames == 0 &&
            jabber_frames   == 0 &&
            trans_octets    == 0 &&
            // HIST
            frames_undersize == 0 &&
            frames_64        == 0 &&
            frames_65_127    == 0 &&
            frames_128_255   == 0 &&
            frames_256_511   == 0 &&
            frames_512_1023  == 0 &&
            frames_1024_1518 == 0 &&
            frames_over_1518 == 0 &&
            frames_1519_2047 == 0 &&
            frames_2048_4095 == 0 &&
            frames_4096_8191 == 0 &&
            frames_over_8191 == 0
        );
    endfunction

    virtual function void set_regmodel(uvm_rx_mac_lite::regmodel#(RX_MAC_COUNT) model);
        regmodel = model;
    endfunction

    virtual function string convert2string();
        string format = "BASE\n\ttrfc %0d cfc %0d dfc %0d bodfc %0d oroc %0d\n\tRFC\n\tcrc_err %0d over_mtu %0d below_min %0d bcast_frames %0d mcast_frames %0d fragment_frames %0d jabber_frames %0d trans_octets %0d\n\tHIST\n\tframes_undersize %0d frames_64 %0d frames_65_127 %0d frames_128_255 %0d frames_256_511 %0d frames_512_1023 %0d frames_1024_1518 %0d frames_over_1518 %0d frames_1519_2047 %0d frames_2048_4095 %0d frames_4096_8191 %0d frames_over_8191 %0d";
        return $sformatf(format, trfc, cfc, dfc, bodfc, oroc, crc_err, over_mtu, below_min, bcast_frames, mcast_frames, fragment_frames, jabber_frames, trans_octets, frames_undersize, frames_64, frames_65_127, frames_128_255, frames_256_511, frames_512_1023, frames_1024_1518, frames_over_1518, frames_1519_2047, frames_2048_4095, frames_4096_8191, frames_over_8191);
    endfunction

endclass

class read_tx_counters extends uvm_sequence;
    `uvm_object_utils(uvm_network_mod_env::read_tx_counters)

    uvm_tx_mac_lite::regmodel regmodel;

    typedef enum bit [8-1 : 0]
    {
        SAMPLE = 'h1,
        RESET  = 'h2
    } command_e;

    longint unsigned tfc;
    longint unsigned toc;
    longint unsigned sfc;
    longint unsigned soc;
    longint unsigned dfc;
    longint unsigned liec;
    longint unsigned lnec;

    function new(string name = "read_tx_counters");
        super.new(name);
    endfunction

    virtual task send_command(command_e command);
        uvm_status_e status;
        regmodel.command.write(status, command);
    endtask

    virtual task read_counter(uvm_reg reg_counter_l, uvm_reg reg_counter_h, output longint unsigned output_value);
        uvm_status_e   status;
        uvm_reg_data_t data;
        reg_counter_l.read(status, data);
        output_value[32-1 : 0] = data;
        reg_counter_h.read(status, data);
        output_value[64-1 : 32] = data;
    endtask

    virtual task reset();
        send_command(RESET);
    endtask

    virtual task body();
        send_command(SAMPLE);

        #(30ns);

        fork
            read_counter(regmodel.tfcl , regmodel.tfch , tfc);
            read_counter(regmodel.tocl , regmodel.toch , toc);
            read_counter(regmodel.sfcl , regmodel.sfch , sfc);
            read_counter(regmodel.socl , regmodel.soch , soc);
            read_counter(regmodel.dfcl , regmodel.dfch , dfc);
            read_counter(regmodel.liecl, regmodel.liech, liec);
            read_counter(regmodel.lnecl, regmodel.lnech, lnec);
        join
    endtask

    virtual function bit zero();
        return (
            tfc  == 0 &&
            toc  == 0 &&
            sfc  == 0 &&
            soc  == 0 &&
            dfc  == 0 &&
            liec == 0 &&
            lnec == 0
        );
    endfunction

    virtual function void set_regmodel(uvm_tx_mac_lite::regmodel model);
        regmodel = model;
    endfunction

    virtual function string convert2string();
        string format = "tfc %0d toc %0d sfc %0d soc %0d dfc %0d liec %0d lnec %0d";
        return $sformatf(format, tfc, toc, sfc, soc, dfc, liec, lnec);
    endfunction

endclass
