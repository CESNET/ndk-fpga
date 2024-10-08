// sequence_set.sv Sequence generating user defined MI transactions
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// This MI sequence define bus functionality
class sequence_mi#(DATA_WIDTH, ADDR_WIDTH, CLK_PERIOD, META_WIDTH = 0) extends uvm_mi::sequence_slave_sim#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_mi2axi4lite::sequence_mi #(DATA_WIDTH, ADDR_WIDTH, CLK_PERIOD, META_WIDTH))

    function new (string name = "sequence_mi");
        super.new(name);
    endfunction

    // In this task you have to define how the MI transactions will look like
    virtual task create_sequence_item();
        uvm_mi::sequence_item_response #(DATA_WIDTH) rsp;
        rsp = uvm_mi::sequence_item_response #(DATA_WIDTH)::type_id::create("rsp");

        // Write request (Default value of BE = '1)
        #(10*CLK_PERIOD)
        // Write to address 0
        write(32'h0, 32'h1);
        #(5*CLK_PERIOD)
        // Write to address 0
        write(32'h4, 32'h2);
        #(5*CLK_PERIOD)
        // Write to address 0
        write(32'h8, 32'h3);
        #(5*CLK_PERIOD)
        // Read request (Default value of BE = '1)
        // Read from address 0
        //      ADDR
        read(32'h0);
        // Read from address 4
        read(32'h4);
        // Read from address 8
        read(32'h8);

        // Print last three read responses
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);

        #(50*CLK_PERIOD)
        // Read request (Default value of BE = '1)
        // Read from address 0
        //      ADDR
        read(32'h0);
        // Read from address 4
        read(32'h4);
        // Read from address 8
        read(32'h8);

        // Print last three read responses
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);

    endtask

endclass
