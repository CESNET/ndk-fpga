//-- generator.sv
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class generator #(ITEM_WIDTH, META_WIDTH, SIDE, ENDPOINT_TYPE, PCIE_T) extends uvm_component;
    `uvm_component_param_utils(uvm_pcie_adapter::generator #(ITEM_WIDTH, META_WIDTH, SIDE, ENDPOINT_TYPE, PCIE_T))

    localparam TYPE_POS = (SIDE == "DOWN") ? 128 : 32;
    localparam LEN_POS  = (SIDE == "DOWN") ? 106 : 10;

    uvm_seq_item_pull_port #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH), uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) seq_item_port_data;

    mailbox#(uvm_logic_vector::sequence_item#(META_WIDTH))       logic_vector_export;
    mailbox#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) logic_vector_array_export;

    uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data;
    uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data_new;
    uvm_logic_vector::sequence_item#(META_WIDTH)       meta;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);

        seq_item_port_data        = new("seq_item_port_data", this);
        logic_vector_export       = new(1);
        logic_vector_array_export = new(1);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);

        logic mode;

        forever begin
            // Get new sequence item to drive to interface
            seq_item_port_data.get_next_item(data);

            $cast(data_new, data.clone());

            assert(std::randomize(mode) with {mode dist {1'b1 :/ 50, 1'b0 :/ 50}; });

            meta = uvm_logic_vector::sequence_item#(META_WIDTH)::type_id::create("meta");

            if (ENDPOINT_TYPE == "R_TILE" && SIDE == "UP") begin
                if (PCIE_T == "CC") begin
                    assert(meta.randomize() with {
                        meta.data[TYPE_POS-1 : TYPE_POS-8] dist {8'b01001010 :/ 100};
                        if (int'(data_new.size()) == 1024)
                            {meta.data[LEN_POS-1 : LEN_POS-10] == '0};
                        else
                            {meta.data[LEN_POS-1 : LEN_POS-10] == int'(data_new.size())};
                    });
                end else begin
                    assert(meta.randomize() with {
                        meta.data[TYPE_POS-1 : TYPE_POS-8] dist {8'b00000000 :/ 25, 8'b00100000 :/ 25, 8'b01000000 :/ 25, 8'b01100000 :/ 25};
                        if (int'(data_new.size()) == 1024)
                            {meta.data[LEN_POS-1 : LEN_POS-10] == '0};
                        else
                            {meta.data[LEN_POS-1 : LEN_POS-10] == int'(data_new.size())};
                    });
                end
            end else begin
                if (mode == 1'b1)
                    assert(meta.randomize() with {
                        meta.data[TYPE_POS-1 : TYPE_POS-8] dist {8'b00001010 :/ 13, 8'b01001010 :/ 13, 8'b00001011 :/ 13, 8'b01001011 :/ 13};
                        if (int'(data_new.size()) == 1024)
                            {meta.data[LEN_POS-1 : LEN_POS-10] == '0};
                        else
                            {meta.data[LEN_POS-1 : LEN_POS-10] == int'(data_new.size())};
                    });
                else
                    assert(meta.randomize() with {
                        meta.data[TYPE_POS-1 : TYPE_POS-8] != 8'b00001010; meta.data[TYPE_POS-1 : TYPE_POS-8] != 8'b01001010; meta.data[TYPE_POS-1 : TYPE_POS-8] != 8'b00001011; meta.data[TYPE_POS-1 : TYPE_POS-8] != 8'b01001011;
                        if (int'(data_new.size()) == 1024)
                            {meta.data[LEN_POS-1 : LEN_POS-10] == '0};
                        else
                            {meta.data[LEN_POS-1 : LEN_POS-10] == int'(data_new.size())};

                    });
            end

            logic_vector_export.put(meta);
            logic_vector_array_export.put(data_new);

            seq_item_port_data.item_done();
        end
    endtask

endclass