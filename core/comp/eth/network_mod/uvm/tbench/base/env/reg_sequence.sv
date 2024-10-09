//-- reg_sequnece.sv: Virtual sequence
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

class read_rx_counters#(RX_MAC_COUNT) extends uvm_sequence;
    `uvm_object_param_utils(uvm_network_mod_env::read_rx_counters#(RX_MAC_COUNT))

    uvm_rx_mac_lite::regmodel#(RX_MAC_COUNT) regmodel;
    logic [64-1:0] trfc;
    logic [64-1:0] cfc;
    logic [64-1:0] dfc;
    logic [64-1:0] bodfc;
    logic [64-1:0] oroc;

    logic [64-1:0] crc_err;
    logic [64-1:0] over_mtu_addr;
    logic [64-1:0] below_min_addr;
    logic [64-1:0] bcast_frames_addr;
    logic [64-1:0] mcast_frames_addr;
    logic [64-1:0] fragment_frames_addr;
    logic [64-1:0] jabber_frames_addr;
    logic [64-1:0] trans_octets_addr;
    logic [64-1:0] frames_64_addr;
    logic [64-1:0] frames_65_127_addr;
    logic [64-1:0] frames_128_255_addr;
    logic [64-1:0] frames_256_511_addr;
    logic [64-1:0] frames_512_1023_addr;
    logic [64-1:0] frames_1024_1518_addr;
    logic [64-1:0] frames_over_1518_addr;
    logic [64-1:0] frames_below_64_addr; 

    function new(string name = "mi_sequence");
        super.new(name);
    endfunction


    virtual task reset();
        uvm_status_e  status_cmd;
        regmodel.command.write(status_cmd, 'h2);
    endtask

    virtual task body();
        uvm_status_e   status_cmd;
        uvm_reg_data_t data_cmd;
        regmodel.command.write(status_cmd, 'h1);
        #(30ns);

        fork
            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.base.trfcl.read(status, data);
                trfc[32-1:0] = data;
                regmodel.base.trfch.read(status, data);
                trfc[64-1:32] = data;
            end
            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.base.cfcl.read(status, data);
                cfc[32-1:0] = data;
                regmodel.base.cfch.read(status, data);
                cfc[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.base.dfcl.read(status, data);
                dfc[32-1:0] = data;
                regmodel.base.dfch.read(status, data);
                dfc[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.base.bodfcl.read(status, data);
                bodfc[32-1:0] = data;
                regmodel.base.bodfch.read(status, data);
                bodfc[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.base.orocl.read(status, data);
                oroc[32-1:0] = data;
                regmodel.base.oroch.read(status, data);
                oroc[64-1:32] = data;
            end
        join

        regmodel.command.write(status_cmd, 'h1);
        #(30ns);

        fork
            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.crc_err_l.read(status, data);
                crc_err[32-1:0] = data;
                regmodel.rfc.crc_err_h.read(status, data);
                crc_err[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.over_mtu_l_addr.read(status, data);
                over_mtu_addr[32-1:0] = data;
                regmodel.rfc.over_mtu_h_addr.read(status, data);
                over_mtu_addr[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.below_min_l_addr.read(status, data);
                below_min_addr[32-1:0] = data;
                regmodel.rfc.below_min_h_addr.read(status, data);
                below_min_addr[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.bcast_frames_l_addr.read(status, data);
                bcast_frames_addr[32-1:0] = data;
                regmodel.rfc.bcast_frames_h_addr.read(status, data);
                bcast_frames_addr[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.mcast_frames_l_addr.read(status, data);
                mcast_frames_addr[32-1:0] = data;
                regmodel.rfc.mcast_frames_h_addr.read(status, data);
                mcast_frames_addr[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.fragment_frames_l_addr.read(status, data);
                fragment_frames_addr[32-1:0] = data;
                regmodel.rfc.fragment_frames_h_addr.read(status, data);
                fragment_frames_addr[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.jabber_frames_l_addr.read(status, data);
                jabber_frames_addr[32-1:0] = data;
                regmodel.rfc.jabber_frames_h_addr.read(status, data);
                jabber_frames_addr[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.trans_octets_l_addr.read(status, data);
                trans_octets_addr[32-1:0] = data;
                regmodel.rfc.trans_octets_h_addr.read(status, data);
                trans_octets_addr[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.frames_64_l_addr.read(status, data);
                frames_64_addr[32-1:0] = data;
                regmodel.rfc.frames_64_h_addr.read(status, data);
                frames_64_addr[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.frames_65_127_l_addr.read(status, data);
                frames_65_127_addr[32-1:0] = data;
                regmodel.rfc.frames_65_127_h_addr.read(status, data);
                frames_65_127_addr[64-1:32] = data;
            end
        
            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.frames_128_255_l_addr.read(status, data);
                frames_128_255_addr[32-1:0] = data;
                regmodel.rfc.frames_128_255_h_addr.read(status, data);
                frames_128_255_addr[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.frames_256_511_l_addr.read(status, data);
                frames_256_511_addr[32-1:0] = data;
                regmodel.rfc.frames_256_511_h_addr.read(status, data);
                frames_256_511_addr[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.frames_512_1023_l_addr.read(status, data);
                frames_512_1023_addr[32-1:0] = data;
                regmodel.rfc.frames_512_1023_h_addr.read(status, data);
                frames_512_1023_addr[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.frames_1024_1518_l_addr.read(status, data);
                frames_1024_1518_addr[32-1:0] = data;
                regmodel.rfc.frames_1024_1518_h_addr.read(status, data);
                frames_1024_1518_addr[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.frames_over_1518_l_addr.read(status, data);
                frames_over_1518_addr[32-1:0] = data;
                regmodel.rfc.frames_over_1518_h_addr.read(status, data);
                frames_over_1518_addr[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.rfc.frames_below_64_l_addr.read(status, data);
                frames_below_64_addr[32-1:0] = data;
                regmodel.rfc.frames_below_64_h_addr.read(status, data);
                frames_below_64_addr[64-1:32] = data;
            end
        join
    endtask

    function void set_regmodel(uvm_rx_mac_lite::regmodel#(RX_MAC_COUNT) model);
        regmodel = model;
    endfunction
endclass


class read_tx_counters extends uvm_sequence;
    `uvm_object_param_utils(uvm_network_mod_env::read_tx_counters)

    uvm_tx_mac_lite::regmodel regmodel;
    logic [64-1:0] tfc;
    logic [64-1:0] soc;
    logic [64-1:0] dfc;
    logic [64-1:0] sfc;

    function new(string name = "mi_sequence");
        super.new(name);
    endfunction

    virtual task reset();
        uvm_status_e  status_cmd;
        regmodel.command.write(status_cmd, 'h2);
    endtask

    virtual task body();
        uvm_status_e   status_cmd;
        regmodel.command.write(status_cmd, 'h1);

        fork
            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.tfcl.read(status, data);
                tfc[32-1:0] = data;
                regmodel.tfch.read(status, data);
                tfc[64-1:32] = data;
            end
            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.socl.read(status, data);
                soc[32-1:0] = data;
                regmodel.soch.read(status, data);
                soc[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.dfcl.read(status, data);
                dfc[32-1:0] = data;
                regmodel.dfch.read(status, data);
                dfc[64-1:32] = data;
            end

            begin
                uvm_status_e   status;
                uvm_reg_data_t data;
                regmodel.sfcl.read(status, data);
                sfc[32-1:0] = data;
                regmodel.sfch.read(status, data);
                sfc[64-1:32] = data;
            end
        join
    endtask

    function void set_regmodel(uvm_tx_mac_lite::regmodel model);
        regmodel = model;
    endfunction
endclass

