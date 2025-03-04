// model.sv: Model of implementation
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class model #(int unsigned RX_ITEMS, int unsigned TX_ITEMS, int unsigned ITEM_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_mvb_shakedown::model #(RX_ITEMS, TX_ITEMS, ITEM_WIDTH))

    // Model inputs
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(ITEM_WIDTH)) in_data;
    uvm_tlm_analysis_fifo #(int unsigned)                                  in_port_number;

    // Model outputs
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(ITEM_WIDTH)) out[TX_ITEMS];

    // Port data queue
    uvm_logic_vector::sequence_item #(ITEM_WIDTH) port_data[$ : TX_ITEMS];

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        in_data        = new("in_data", this);
        in_port_number = new("in_port_number", this);
        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            out[i] = new($sformatf("out_%0d", i), this);
        end
    endfunction

    task run_phase(uvm_phase phase);
        uvm_logic_vector::sequence_item #(ITEM_WIDTH) out_item;

        int unsigned port_number;

        forever begin
            // Get the port number from which an item was read
            in_port_number.get(port_number);

            //   Direction | Dequeue <------------------------------------------- Enqueue |
            //             |===================================|                          |
            //       Ports |   P0   |   P1   |   P2   |   P*   |                          |
            //             |========+========+========+========+==========================|
            //   `in_data` | [item] | [item] | [item] | [item] | [item] [item] [item] ... |
            //             |==============================================================|
            //                  |        |        |        |
            //                  V        V        V        V
            //             |===================================|
            // `port_data` | [item] | [item] | [item] | [item] |
            //             |========+========+========+========|
            //     Indices |   I0   |   I1   |   I2   |   I*   |
            //             |===================================|
            //   Direction | Enqueue ----------------> Dequeue |
            //
            //             | < ---------- TX_ITEMS --------- > |

            // Ensure there is an item on the port
            while (port_number+1 > port_data.size()) begin
                uvm_logic_vector::sequence_item #(ITEM_WIDTH) temp_item;
                in_data.get(temp_item);
                port_data.push_back(temp_item);
            end

            out_item = uvm_logic_vector::sequence_item #(ITEM_WIDTH)::type_id::create("out_item");

            // Read an item from the port
            out_item = port_data[port_number];
            port_data.delete(port_number);

            out[port_number].write(out_item);
        end
    endtask

endclass
