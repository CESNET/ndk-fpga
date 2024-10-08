// sequence.sv
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_item extends uvm_sequence_item;
    `uvm_object_param_utils(uvm_tx_dma_calypte_cq::sequence_item)

    localparam ITEM_WIDTH = 8;
    localparam META_WIDTH = 24;

    rand logic [ITEM_WIDTH-1:0] m_packet[];
    rand logic [META_WIDTH-1:0] m_meta;

    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "do_copy:", "Failed to cast transaction object.")
            return;
        end
        // Now copy all attributes
        super.do_copy(rhs);
        m_packet = rhs_.m_packet;
        m_meta   = rhs_.m_meta;
    endfunction: do_copy

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item rhs_;
        bit ret;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret = super.do_compare(rhs, comparer);
        // Using simple equivalence operator (faster).
        ret &= (m_packet === rhs_.m_packet);
        ret &= (m_meta  === rhs_.m_meta);
        return ret;
    endfunction: do_compare

    // Convert transaction into human readable form.
    function string convert2string();
        return convert2block(8);
    endfunction

    function string convert2block(int unsigned region_width);
        string ret;

        ret = $sformatf("%s\n\tdma_rx_ll_rx::sequence_item meta %h size %0d", super.convert2string(), m_meta, m_packet.size());
        for (int unsigned it = 0; it < m_packet.size(); it++) begin
            if (it % (region_width*4) == 0) begin
                ret = {ret, $sformatf("\n\t\t%x", m_packet[it])};
            end else if (it % (region_width) == 0) begin
                ret = {ret, $sformatf("    %x", m_packet[it])};
            end else begin
                ret = {ret, $sformatf(" %x", m_packet[it])};
            end
        end
        return ret;
    endfunction

    function int unsigned size();
        return m_packet.size();
    endfunction
endclass

