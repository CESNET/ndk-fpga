// model_data_comparer.sv: Model data comparer
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class model_data_comparer #(int unsigned MFB_ITEM_WIDTH) extends uvm_common::comparer_base_ordered #(model_data_item #(MFB_ITEM_WIDTH), uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH));
    `uvm_object_param_utils(uvm_mfb_frame_extender::model_data_comparer #(MFB_ITEM_WIDTH))

    // Constructor
    function new(string name = "model_data_comparer");
        super.new(name);
    endfunction

    function int unsigned compare(model_data_item #(MFB_ITEM_WIDTH) tr_model, uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) tr_dut);
        if (tr_model.size() !== tr_dut.size()) begin
            return 0;
        end

        for (int unsigned i = tr_model.ext_size; i < tr_model.data.size(); i++) begin
            if (tr_model.data[i] !== tr_dut.data[i]) begin
                return 0;
            end
        end

        return 1;
    endfunction

endclass
