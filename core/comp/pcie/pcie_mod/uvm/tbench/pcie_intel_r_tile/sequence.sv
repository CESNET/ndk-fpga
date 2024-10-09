// sequence.sv: AVST credit control sequence
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_returning #(int unsigned UPDATE_CNT_WIDTH) extends uvm_avst_crdt::sequence_rx_base #(UPDATE_CNT_WIDTH);
    `uvm_object_param_utils(uvm_pcie_intel_r_tile::sequence_returning #(UPDATE_CNT_WIDTH))
    `uvm_declare_p_sequencer(uvm_pcie_intel_r_tile::sequencer #(UPDATE_CNT_WIDTH))

    // Constructor
    function new(string name = "sequence_returning");
        super.new(name);
    endfunction

    task send_transaction();
        logic randomization_result;
        start_item(req);

        randomization_result = req.randomize() with {
            init == 1'b0;
            update_cnt inside {[0 : p_sequencer.total]};
        };
        assert(randomization_result)
        else begin
            `uvm_fatal(this.get_full_name(), "\n\tSequence randomization error")
        end

        finish_item(req);
        get_response(rsp);

        // Reduce total
        p_sequencer.total -= (req.update === 1'b1) ? req.update_cnt : 0;
    endtask

endclass

class sequence_returning_hdr extends sequence_returning #(2);
    `uvm_object_utils(uvm_pcie_intel_r_tile::sequence_returning_hdr)

    // Constructor
    function new(string name = "sequence_returning_hdr");
        super.new(name);
    endfunction

endclass

class sequence_returning_data extends sequence_returning #(4);
    `uvm_object_utils(uvm_pcie_intel_r_tile::sequence_returning_data)

    // Constructor
    function new(string name = "sequence_returning_data");
        super.new(name);
    endfunction

endclass
