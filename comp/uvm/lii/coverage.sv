//-- lii_coverage.sv: Coverage for lii interface.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>
//--
//-- SPDX-License-Identifier: BSD-3-Clause

class coverage #(int unsigned DATA_WIDTH, int unsigned META_WIDTH, int unsigned SOF_WIDTH) extends uvm_subscriber#(sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH));

    sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH) seq_item;

    covergroup m_cov_rdy_sig;
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
        // -- Sequence of RDY.
        rdy : coverpoint seq_item.rdy {
            bins short   = (0 => 1 => 0);
            bins longer  = (0 => 1[*2:16]  => 0);
            bins long    = (0 => 1[*17:32] => 0);
            bins longest = default;
        }
    endgroup

    covergroup m_cov_bytes_vld_sig;
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------
        // -- Sequence of BYTES_VLD.
        bytes_vld : coverpoint seq_item.bytes_vld {
            bins aligned   = {3'b100};
            bins unaligned = {3'b001, 3'b010, 3'b011};
            bins wrong     = {3'b101, 3'b110, 3'b111};
        }
    endgroup

    function new (string name, uvm_component parent = null);
        super.new(name, parent);
        m_cov_rdy_sig = new();
        m_cov_bytes_vld_sig = new();
    endfunction

    virtual function void write(sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH) t);
        seq_item = t;
        m_cov_rdy_sig.sample();
        if (seq_item.eof == 1'b1) begin
            m_cov_bytes_vld_sig.sample();
        end
    endfunction

    function void display();
        $write("Ready signals coverage %f %% byte valid signals coverage %f %%\n", m_cov_rdy_sig.get_inst_coverage(), m_cov_bytes_vld_sig.get_inst_coverage());
    endfunction

endclass
