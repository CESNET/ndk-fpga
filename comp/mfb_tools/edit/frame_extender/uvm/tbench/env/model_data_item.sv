// model_data_item.sv: Model data item
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class model_data_item #(int unsigned MFB_ITEM_WIDTH) extends uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH);
    `uvm_object_param_utils(uvm_mfb_frame_extender::model_data_item #(MFB_ITEM_WIDTH))

    int unsigned ext_size;

    // Constructor
    function new(string name = "model_data_item");
        super.new(name);
    endfunction

    // -------------------- //
    // Common UVM functions //
    // -------------------- //

    // Properly copies all transaction attributes
    function void do_copy(uvm_object rhs);
        model_data_item #(MFB_ITEM_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_copy:", "Failed to cast transaction object.")
            return;
        end

        // Copies all attributes
        super.do_copy(rhs);
        ext_size = rhs_.ext_size;
    endfunction

    // Properly compares all transaction attributes representing output pins
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        model_data_item #(MFB_ITEM_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        // Compares all attributes that maters
        return (
            (super.do_compare(rhs, comparer)) &&
            (ext_size === rhs_.ext_size)
        );
    endfunction

    // Visualize the sequence item to string
    function string convert2string();
        string output_string;

        output_string = $sformatf("\n\tmodel_data_item:\n\tdata: %s \n\text_size: %0d \n",
                            super.convert2string(),
                            ext_size
                        );

        return output_string;
    endfunction

endclass
