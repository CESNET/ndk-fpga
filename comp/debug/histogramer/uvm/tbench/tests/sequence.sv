//-- sequence.sv: Package with global constants
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`include "const.sv"

class sequence_base #(DATA_WIDTH, INPUT_WIDTH, ADDR_WIDTH) extends uvm_sequence #(uvm_logic_vector::sequence_item #(DATA_WIDTH));
    `uvm_object_utils(test::sequence_base#(DATA_WIDTH, INPUT_WIDTH, ADDR_WIDTH))

    uvm_logic_vector::sequence_item #(DATA_WIDTH) req;

    // Constructor - creates new instance of this class
    function new(string name = "sequence_base");
        super.new(name);

        req = uvm_logic_vector::sequence_item#(DATA_WIDTH)::type_id::create("req");
    endfunction

    task write_req(logic [INPUT_WIDTH - 1 : 0] val);
        logic read_req = 0;
        logic [ADDR_WIDTH - 1 : 0] addr = 0;

        start_item(req);
        req.data = {read_req, val, addr};
        finish_item(req);
    endtask

    task read_req(logic [ADDR_WIDTH - 1 : 0] addr);
        logic read_req = 1;
        logic [INPUT_WIDTH - 1 : 0] val = 0;

        start_item(req);
        req.data = {read_req, val, addr};
        finish_item(req);
    endtask
endclass

class sequence_read #(DATA_WIDTH, INPUT_WIDTH, ADDR_WIDTH) extends sequence_base #(DATA_WIDTH, INPUT_WIDTH, ADDR_WIDTH);
    `uvm_object_utils(test::sequence_read#(DATA_WIDTH, INPUT_WIDTH, ADDR_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "sequence_simple_const");
        super.new(name);
    endfunction

    // Generates transactions
    task body;
        for (int addr = 0 ; addr < 2 ** ADDR_WIDTH; addr ++) begin
            read_req(addr);
        end
        // Test clear by read
        for (int addr = 0 ; addr < 2 ** ADDR_WIDTH; addr ++) begin
            read_req(addr);
        end
    endtask

endclass

class sequence_rand #(DATA_WIDTH, INPUT_WIDTH, ADDR_WIDTH, READ_OCCURENCE, WRITE_OCCURENCE) extends sequence_base #(DATA_WIDTH, INPUT_WIDTH, ADDR_WIDTH);
    `uvm_object_utils(test::sequence_rand#(DATA_WIDTH, INPUT_WIDTH, ADDR_WIDTH, READ_OCCURENCE, WRITE_OCCURENCE))

    rand bit                            read;
    rand logic [ADDR_WIDTH - 1 : 0]     addr;
    rand logic [INPUT_WIDTH - 1 : 0]    val;

    constraint constr {
        read dist {
            0 := WRITE_OCCURENCE,
            1 := READ_OCCURENCE
        };
    }

    function new(string name = "sequence_random");
        super.new(name);
    endfunction

    task body;
        req = uvm_logic_vector::sequence_item#(DATA_WIDTH)::type_id::create("req");
        `uvm_info(get_full_name(), "sequence_rand is running", UVM_DEBUG)

        if (read) begin

            read_req(addr);

        end else begin

            write_req(val);

        end
    endtask

endclass


