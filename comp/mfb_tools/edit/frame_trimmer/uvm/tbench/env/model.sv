// model.sv: Model of implementation
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class model #(int unsigned ITEM_WIDTH, int unsigned PKT_MTU) extends uvm_component;
    `uvm_component_param_utils(uvm_mfb_frame_trimmer::model #(ITEM_WIDTH, PKT_MTU))

    // ------ //
    // Inputs //
    // ------ //

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH))    in_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(1+$clog2(PKT_MTU+1))) in_trim;

    // ------- //
    // Outputs //
    // ------- //

    uvm_analysis_port #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)) out_data;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        in_data  = new("in_data", this);
        in_trim  = new("in_trim", this);
        out_data = new("out_data", this);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)          in_data_item;
        uvm_logic_vector::sequence_item       #(1+$clog2(PKT_MTU+1)) in_trim_item;
        uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)          out_data_item;

        bit          trim_en;
        int unsigned trim_len;

        forever begin
            in_data.get(in_data_item);
            in_trim.get(in_trim_item);

            out_data_item = uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)::type_id::create("out_data_item");

            trim_len = in_trim_item.data[$clog2(PKT_MTU+1)  -1 -: $clog2(PKT_MTU+1)];
            trim_en  = in_trim_item.data[1+$clog2(PKT_MTU+1)-1 -: 1];

            if (trim_en === 1'b1) begin
                assert(trim_len <= in_data_item.size())
                else begin
                    `uvm_fatal(get_full_name(), $sformatf("\n\tThe TRIM length (%0d) is bigger than the data frame length (%0d)\n", trim_len, in_data_item.size()))
                end

                // Trim input data
                out_data_item.data = new[trim_len](in_data_item.data);
            end
            else begin
                out_data_item.data = in_data_item.data;
            end

            out_data.write(out_data_item);
        end
    endtask

endclass
