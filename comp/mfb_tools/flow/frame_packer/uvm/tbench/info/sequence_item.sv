// pkg.sv
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


// This class represents high level transaction, which can be reusable for other components.
class sequence_item #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH) extends uvm_sequence_item;
    // Registration of object tools.
    `uvm_object_param_utils(uvm_meta::sequence_item #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH))

    // -----------------------
    // Variables.
    // -----------------------
    localparam MVB_LEN_WIDTH = $clog2(USR_RX_PKT_SIZE_MAX+1);
    localparam MVB_CHANNEL_WIDTH = $clog2(RX_CHANNELS);

     rand logic [MVB_LEN_WIDTH-1:0]       packet_size;
     rand logic [HDR_META_WIDTH-1:0]      meta;
     rand logic [MVB_CHANNEL_WIDTH-1:0]   channel;
     rand logic                           discard;


    // Constructor - creates new instance of this class
    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    // -----------------------
    // Common UVM functions.
    // -----------------------

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "do_copy:", "Failed to cast transaction object.")
            return;
        end
        // Now copy all attributes
        super.do_copy(rhs);
        packet_size = rhs_.packet_size;
        meta        = rhs_.meta;
        channel     = rhs_.channel;
        discard     = rhs_.discard;
    endfunction: do_copy

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret;
        sequence_item #(USR_RX_PKT_SIZE_MAX, RX_CHANNELS, HDR_META_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret  = super.do_compare(rhs, comparer);
        ret &= (packet_size == rhs_.packet_size);
        ret &= (meta        == rhs_.meta);
        ret &= (channel     == rhs_.channel);
        ret &= (discard     == rhs_.discard);

        return ret;
    endfunction: do_compare

    // Convert transaction into human readable form.
    function string convert2string();
        string ret;

        ret = $sformatf("\tPacket_size : %h\n\tMeta : %h\n\tChannel : %0d\n\tDiscard : %b\n", packet_size, meta, channel, discard);

        return ret;
    endfunction
endclass

