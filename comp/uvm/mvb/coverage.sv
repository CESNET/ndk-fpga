//-- mvb_coverage.sv: Coverage for mvb interface.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
//--
//-- SPDX-License-Identifier: BSD-3-Clause

class coverage #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_subscriber#(sequence_item #(ITEMS, ITEM_WIDTH));
    `uvm_component_param_utils(uvm_mvb::coverage #(ITEMS, ITEM_WIDTH))

    sequence_item #(ITEMS, ITEM_WIDTH) seq_item;
    logic [ITEM_WIDTH-1 : 0] item;
    logic vld;

    covergroup m_cov_seq_item_data;
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
        // -- Coverage of transferred data.
        data : coverpoint item {
            bins low    = {[ITEM_WIDTH'(0)                                  : ITEM_WIDTH'(2)**(ITEM_WIDTH-8)]};
            bins mid    = {[ITEM_WIDTH'(2)**(ITEM_WIDTH-8)+1                : ITEM_WIDTH'(2)**(ITEM_WIDTH-2)]};
            bins higth  = {[ITEM_WIDTH'(2)**(ITEM_WIDTH-2)+1                : $]};
        }

        vld_transfered_items : coverpoint vld iff (seq_item.src_rdy & seq_item.dst_rdy){
            bins valid      = {1};
            bins non_valid  = {0};
        }

        valid_transfered_data : cross data, vld_transfered_items;

    endgroup

    covergroup m_cov_rdy_sig;
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
        // -- Sequence of SRC_RDY.
        src_rdy : coverpoint seq_item.src_rdy {
            bins short   = (0 => 1 => 0);
            bins longer  = (0 => 1[*2:16]  => 0);
            bins long    = (0 => 1[*17:32] => 0);
            bins longest = default;
        }
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
        // -- Sequence of DST_RDY.
        dst_rdy : coverpoint seq_item.dst_rdy {
            bins short   = (0 => 1 => 0);
            bins longer  = (0 => 1[*2:16]  => 0);
            bins long    = (0 => 1[*17:32] => 0);
            bins longest = default;
        }
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
        // -- Sequence of transferred transactions.
        read_sequence : coverpoint seq_item.src_rdy & seq_item.dst_rdy {
            bins short   = (0 => 1 => 0);
            bins longer  = (0 => 1[*2:16]   => 0);
            bins long    = (0 => 1[*17:32]  => 0);
            bins longest = default;
        }

    endgroup


    function new (string name, uvm_component parent = null);
        super.new(name, parent);
        m_cov_rdy_sig = new();
        m_cov_seq_item_data = new();
    endfunction

    virtual function void write(sequence_item #(ITEMS, ITEM_WIDTH) t);
        seq_item = t;
        m_cov_rdy_sig.sample();
        for (int i = 0; i<ITEMS; i++) begin
            item = t.data[i];
            vld = t.vld[i];
            m_cov_seq_item_data.sample();
        end
    endfunction

    function void display();
        $write("Ready signals coverage %f %%\nData coverage %f %%", m_cov_rdy_sig.get_inst_coverage(), m_cov_seq_item_data.get_inst_coverage());
    endfunction

endclass
