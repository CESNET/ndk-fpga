// coverage.sv: Functional coverage of tests
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class coverage #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)
    extends uvm_subscriber #(uvm_mfb::sequence_item #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH));

    `uvm_component_param_utils(uvm_tx_dma_calypte::coverage #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))

    covergroup m_cov_seq_item_sof_eof_count with function sample(uvm_mfb::sequence_item #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) seq_item);
        // -----------------------------------------------------------------------------
        // Coverage of packet begins
        // -----------------------------------------------------------------------------
        sof_count : coverpoint seq_item.sof iff (seq_item.src_rdy & seq_item.dst_rdy) {
            bins two_packets                 = {2'b11};
            bins one_packet                  = {2'b01};
            illegal_bins forbidden_pkt_start = {2'b10};
        }

        eof_count : coverpoint seq_item.eof iff (seq_item.src_rdy & seq_item.dst_rdy) {
            bins two_packets  = {2'b11};
            bins one_packet_0 = {2'b01};
            bins one_packet_1 = {2'b10};
        }

        two_whole_packets : cross sof_count, eof_count;
    endgroup

    function new (string name, uvm_component parent = null);
        super.new(name, parent);
        if (MFB_REGIONS == 2) begin
            m_cov_seq_item_sof_eof_count = new();
        end
    endfunction

    virtual function void write(uvm_mfb::sequence_item #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) t);
        if (MFB_REGIONS == 2) begin
            m_cov_seq_item_sof_eof_count.sample(t);
        end
    endfunction

    function void display();
        if (MFB_REGIONS == 2) begin
            $write("Pkt SOF/EOF counts coverage %f %%\n", m_cov_seq_item_sof_eof_count.get_inst_coverage());
        end
    endfunction
endclass
