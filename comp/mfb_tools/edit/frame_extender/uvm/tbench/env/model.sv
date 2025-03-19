// model.sv: Model of implementation
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class model #(int unsigned MFB_ITEM_WIDTH, int unsigned PKT_MTU, int unsigned USERMETA_WIDTH, int unsigned RX_MVB_ITEM_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_mfb_frame_extender::model #(MFB_ITEM_WIDTH, PKT_MTU, USERMETA_WIDTH, RX_MVB_ITEM_WIDTH))

    // Model inputs
    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH))                   in_data;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item       #(USERMETA_WIDTH))                   in_meta;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item       #(RX_MVB_ITEM_WIDTH-USERMETA_WIDTH)) in_extension;

    // Model outputs
    uvm_analysis_port #(model_data_item #(MFB_ITEM_WIDTH))                 out_data;
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(USERMETA_WIDTH)) out_meta;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        in_data      = new("in_data", this);
        in_meta      = new("in_meta", this);
        in_extension = new("in_extension", this);
        out_data     = new("out_data", this);
        out_meta     = new("out_meta", this);
    endfunction

    task run_phase(uvm_phase phase);
        uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)                   in_data_item;
        uvm_logic_vector::sequence_item       #(USERMETA_WIDTH)                   in_meta_item;
        uvm_logic_vector::sequence_item       #(RX_MVB_ITEM_WIDTH-USERMETA_WIDTH) in_extension_item;

        model_data_item                 #(MFB_ITEM_WIDTH) out_data_item;
        uvm_logic_vector::sequence_item #(USERMETA_WIDTH) out_meta_item;

        bit          ext_en;
        bit          ext_only;
        int unsigned ext_size;
        int unsigned frame_length;

        forever begin
            in_meta     .get(in_meta_item);
            in_extension.get(in_extension_item);

            out_data_item = model_data_item                 #(MFB_ITEM_WIDTH)::type_id::create("out_data_item");
            out_meta_item = uvm_logic_vector::sequence_item #(USERMETA_WIDTH)::type_id::create("out_meta_item");

            ext_en       = in_extension_item.data[1                                      -1 -: 1];
            ext_only     = in_extension_item.data[1+1                                    -1 -: 1];
            ext_size     = in_extension_item.data[$clog2(PKT_MTU+1)+1+1                  -1 -: $clog2(PKT_MTU+1)];
            frame_length = in_extension_item.data[$clog2(PKT_MTU+1)+$clog2(PKT_MTU+1)+1+1-1 -: $clog2(PKT_MTU+1)];

            if (ext_en === 1'b1) begin
                logic [MFB_ITEM_WIDTH-1 : 0] empty[] = new[ext_size];

                if (ext_only === 1'b1) begin
                    out_data_item.data = empty;
                end
                else begin
                    in_data.get(in_data_item);
                    assert_frame_length(in_data_item.size(), frame_length);

                    out_data_item.data = { empty, in_data_item.data };
                end

                out_data_item.ext_size = ext_size;
            end
            else begin
                in_data.get(in_data_item);
                assert_frame_length(in_data_item.data.size(), frame_length);

                out_data_item.data     = in_data_item.data;
                out_data_item.ext_size = 0;
            end

            out_meta_item.data = in_meta_item.data;

            out_data.write(out_data_item);
            out_meta.write(out_meta_item);
        end
    endtask

    function void assert_frame_length(int unsigned actual_frame_length, int unsigned extension_provided_frame_length);
        assert(actual_frame_length === extension_provided_frame_length)
        else begin
            `uvm_fatal(get_full_name(), $sformatf("\n\tThe actual frame length (%0d) differs from the length (%0d) provided through the extension item", actual_frame_length, extension_provided_frame_length))
        end
    endfunction

    function int unsigned used();
        int unsigned result = 0;
        result += in_data.used();
        result += in_meta.used();
        result += in_extension.used();
        return result;
    endfunction

    function void check_phase(uvm_phase phase);
        super.check_phase(phase);

        assert(used() == 0)
        else begin
            `uvm_error(get_full_name(), $sformatf("\n\tSOME TRANSACTIONS ARE STUCK INSIDE THE MODEL\n\tDATA:%0d\n\tMETA:%0d\n\tEXTENSION:%0d", in_data.used(), in_meta.used(), in_extension.used()));
        end
    endfunction

endclass
