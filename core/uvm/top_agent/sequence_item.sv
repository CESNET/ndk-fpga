//-- sequence_item.sv: Item packet information
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


virtual class sequence_item#(int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_common::sequence_item;

    rand logic [ITEM_WIDTH-1:0]      data[];

    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    virtual function void meta2item(logic [META_WIDTH-1:0] meta, uvm_component parent = null);
    endfunction

    virtual function logic [META_WIDTH-1:0] item2meta();
    endfunction

    function void do_copy(uvm_object rhs);
        sequence_item#(ITEM_WIDTH, META_WIDTH)  rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "uvm_app_core_top_agent::sequence_item::do_copy:", "Failed to cast transaction object." );
            return;
        end

        super.do_copy(rhs);
        data = rhs_.data;
    endfunction

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret = 1;

        sequence_item#(ITEM_WIDTH, META_WIDTH)  rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "uvm_app_core_top_agent::sequence_item::do_compare:", "Failed to cast transaction object." );
            return 0;
        end

        ret &= super.do_compare(rhs, comparer);
        ret &= (data === rhs_.data);
        return ret;
    endfunction

    function string convert2string();
        string msg = super.convert2string();

        for (int unsigned it = 0; it < data.size(); it++) begin
            if (it % 32 == 0) begin
                msg = { msg, $sformatf("\n\t%h", data[it])};
            end else if (it % 8 == 0) begin
                msg = { msg, $sformatf("    %h", data[it])};
            end else begin
                msg = { msg, $sformatf(" %h", data[it])};
            end
        end
        return msg;
    endfunction

endclass

                                                                                                                     // CHANNEL_WIDTH + LENGHT_WIDTH + FLAGS  +  MAC_HIT  + TSU WIDTH
class sequence_eth_item#(int unsigned CHANNELS, int unsigned LENGTH_WIDTH, int unsigned ITEM_WIDTH) extends sequence_item#(ITEM_WIDTH, LENGTH_WIDTH + $clog2(CHANNELS) + 10 + 4 + 64);
    `uvm_object_param_utils(uvm_app_core_top_agent::sequence_eth_item#(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH))

    //rand logic [$clog2(CHANNELS)-1:0] channel;
    int unsigned        channel;
    rand logic          error;
    rand logic          error_frame;
    rand logic          error_min_mtu;
    rand logic          error_max_mtu;
    rand logic          error_crc;
    rand logic          error_mac;
    rand logic          broadcast;
    rand logic          multicast;
    rand logic          hit_mac_vld;
    rand logic [4-1:0]  hit_mac;
    rand logic          timestamp_vld;
    rand logic [64-1:0] timestamp;

    constraint c_channels {
        channel inside {[0:CHANNELS-1]};
    }

    function new(string name = "sequence_eth_item");
        super.new(name);
    endfunction

    virtual function void meta2item(logic [META_WIDTH-1:0] meta, uvm_component parent = null);
        logic [LENGTH_WIDTH-1:0] length;
        logic [$clog2(CHANNELS)-1:0] channel;

        {timestamp, timestamp_vld, hit_mac, hit_mac_vld, multicast, broadcast, error_mac, error_crc,
         error_max_mtu, error_min_mtu,error_frame, error, channel, length} = meta;
         this.channel = channel;

         if (data.size() != length) begin
             `uvm_fatal(parent != null ? parent.get_full_name() : "", $sformatf("\n\tData length in metadata(%0d) is not same as data size (%0d)", length, data.size()));
        end
    endfunction

    virtual function logic [META_WIDTH-1:0] item2meta();
        logic [META_WIDTH-1:0] meta;
        logic [LENGTH_WIDTH-1:0] length;
        logic [$clog2(CHANNELS)-1:0] channel;

        channel = this.channel;
        length = data.size();
        meta = {timestamp, timestamp_vld, hit_mac, hit_mac_vld, multicast, broadcast, error_mac, error_crc,
                error_max_mtu, error_min_mtu,error_frame, error, channel, length};
        return meta;
    endfunction


    function void do_unpack(uvm_packer packer);
        int unsigned size;
        super.do_unpack(packer);
        timestamp      = packer.unpack_field(64);
        timestamp_vld  = packer.unpack_field(1);
        hit_mac        = packer.unpack_field(4);
        hit_mac_vld    = packer.unpack_field(1);
        multicast      = packer.unpack_field(1);
        broadcast      = packer.unpack_field(1);
        error_mac      = packer.unpack_field(1);
        error_crc      = packer.unpack_field(1);
        error_max_mtu  = packer.unpack_field(1);
        error_min_mtu  = packer.unpack_field(1);
        error_frame    = packer.unpack_field(1);
        error          = packer.unpack_field(1);
        channel        = packer.unpack_field_int( $clog2(CHANNELS));
        size           = packer.unpack_field_int(LENGTH_WIDTH);
    endfunction


    function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        packer.pack_field(timestamp, 64);
        packer.pack_field(timestamp_vld, 1);
        packer.pack_field(hit_mac, 4);
        packer.pack_field(hit_mac_vld, 1);
        packer.pack_field(multicast, 1);
        packer.pack_field(broadcast, 1);
        packer.pack_field(error_mac, 1);
        packer.pack_field(error_crc, 1);
        packer.pack_field(error_max_mtu, 1);
        packer.pack_field(error_min_mtu, 1);
        packer.pack_field(error_frame, 1);
        packer.pack_field(error, 1);
        packer.pack_field_int(channel, $clog2(CHANNELS));
        packer.pack_field_int(data.size(), LENGTH_WIDTH);
    endfunction



    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_eth_item#(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH)  rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "uvm_app_core_top_agent::sequence_item::do_copy:", "Failed to cast transaction object." )
            return;
        end

        // Now copy all attributes.
        super.do_copy(rhs);
        channel = rhs_.channel;
        error   = rhs_.error;
        error_frame   = rhs_.error_frame;
        error_min_mtu = rhs_.error_min_mtu;
        error_max_mtu = rhs_.error_max_mtu;
        error_crc     = rhs_.error_crc;
        error_mac     = rhs_.error_mac;
        broadcast     = rhs_.broadcast;
        multicast     = rhs_.multicast;
        hit_mac_vld   = rhs_.hit_mac_vld;
        hit_mac       = rhs_.hit_mac;
        timestamp_vld = rhs_.timestamp_vld;
        timestamp     = rhs_.timestamp;
    endfunction

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret = 1;
        sequence_eth_item#(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH)  rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret = super.do_compare(rhs, comparer);
        ret &= (channel       === rhs_.channel);
        ret &= (error         === rhs_.error);
        ret &= (error_frame   === rhs_.error_frame);
        ret &= (error_min_mtu === rhs_.error_min_mtu);
        ret &= (error_max_mtu === rhs_.error_max_mtu);
        ret &= (error_crc     === rhs_.error_crc);
        ret &= (error_mac     === rhs_.error_mac);
        ret &= (broadcast     === rhs_.broadcast);
        ret &= (multicast     === rhs_.multicast);
        ret &= (hit_mac_vld   === rhs_.hit_mac_vld);
        ret &= (hit_mac       === rhs_.hit_mac);
        ret &= (timestamp_vld === rhs_.timestamp_vld);
        ret &= (timestamp     === rhs_.timestamp);
        return ret;
    endfunction

    // Visualize the sequence item to string
    function string convert2string();
        string msg = super.convert2string();

        msg = {msg, $sformatf("\tchannel       %0d\n", channel     )};
        msg = {msg, $sformatf("\terror         %b\n", error        )};
        msg = {msg, $sformatf("\terror_frame   %b\n", error_frame  )};
        msg = {msg, $sformatf("\terror_min_mtu %b\n", error_min_mtu)};
        msg = {msg, $sformatf("\terror_max_mtu %b\n", error_max_mtu)};
        msg = {msg, $sformatf("\terror_crc     %b\n", error_crc    )};
        msg = {msg, $sformatf("\terror_mac     %b\n", error_mac    )};
        msg = {msg, $sformatf("\tbroadcast     %b\n", broadcast    )};
        msg = {msg, $sformatf("\tmulticast     %b\n", multicast    )};
        msg = {msg, $sformatf("\thit_mac_vld   %b\n", hit_mac_vld  )};
        msg = {msg, $sformatf("\thit_mac       %0d\n", hit_mac     )};
        msg = {msg, $sformatf("\ttmimstemp_vld %b\n", timestamp_vld)};
        msg = {msg, $sformatf("\ttimestamp     0x%h\n", timestamp    )};

        return msg;
    endfunction
endclass


class sequence_dma_item#(int unsigned CHANNELS, int unsigned LENGTH_WIDTH, int unsigned DMA_HDR_META_WIDTH, int unsigned ITEM_WIDTH) extends sequence_item#(ITEM_WIDTH, $clog2(CHANNELS) + DMA_HDR_META_WIDTH + LENGTH_WIDTH);
    `uvm_object_param_utils(uvm_app_core_top_agent::sequence_dma_item#(CHANNELS, LENGTH_WIDTH, DMA_HDR_META_WIDTH, ITEM_WIDTH))

    //rand logic [$clog2(CHANNELS)-1:0]   channel;
    int unsigned                        channel;
    rand logic [DMA_HDR_META_WIDTH-1:0] meta;

    constraint c_channels {
        channel inside {[0:CHANNELS-1]};
    }

    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    virtual function void meta2item(logic [META_WIDTH-1:0] meta, uvm_component parent = null);
        logic [LENGTH_WIDTH-1:0]     length;
        logic [$clog2(CHANNELS)-1:0] channel;

        {channel, this.meta, length} = meta;
        this.channel = channel;

         if (data.size() != length) begin
             `uvm_fatal(parent != null ? parent.get_full_name() : "", $sformatf("\n\tData length in metadata(%0d) is not same as data size (%0d)", length, data.size()));
        end
    endfunction


    virtual function logic [META_WIDTH-1:0] item2meta();
        logic [META_WIDTH-1:0] meta;
        logic [LENGTH_WIDTH-1:0] length;

        length = data.size();
        meta = {this.channel, this.meta, length};
        return meta;
    endfunction

    function void do_unpack(uvm_packer packer);
        int unsigned data_size;

        super.do_unpack(packer);
        channel   = packer.unpack_field_int($clog2(CHANNELS));
        meta      = packer.unpack_field    (DMA_HDR_META_WIDTH);
        data_size = packer.unpack_field_int(LENGTH_WIDTH);
    endfunction



    function void do_pack(uvm_packer packer);
        super.do_pack(packer);
        packer.pack_field_int(channel, $clog2(CHANNELS));
        packer.pack_field(meta, DMA_HDR_META_WIDTH);
        packer.pack_field_int(data.size(), LENGTH_WIDTH);
    endfunction

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_dma_item#(CHANNELS, LENGTH_WIDTH, DMA_HDR_META_WIDTH, ITEM_WIDTH)  rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "uvm_app_core_top_agent::sequence_item::do_copy:", "Failed to cast transaction object." )
            return;
        end

        // Now copy all attributes.
        super.do_copy(rhs);
        channel = rhs_.channel;
        meta    = rhs_.meta;
    endfunction

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret = 1;
        sequence_dma_item#(CHANNELS, LENGTH_WIDTH, DMA_HDR_META_WIDTH, ITEM_WIDTH)  rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret = super.do_compare(rhs, comparer);
        ret &= (channel    === rhs_.channel);
        ret &= (meta       === rhs_.meta);
        return ret;
    endfunction

    // Visualize the sequence item to string
    function string convert2string();
        string msg = super.convert2string();

        msg = {msg, $sformatf("\tPACK FORM   0x%h\n",      this.item2meta())};
        msg = {msg, $sformatf("\tchannel       %0d\n", channel )};
        msg = {msg, $sformatf("\tmeta        0x%h\n",  meta    )};
        msg = {msg, super.convert2string()};

        return msg;
    endfunction
endclass

