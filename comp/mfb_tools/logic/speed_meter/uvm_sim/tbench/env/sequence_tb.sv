// sequence_set.sv Sequence generating user defined MI and data transactions
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// This MI sequence define bus functionality
class sequence_mi#(DATA_WIDTH, ADDR_WIDTH, CLK_PERIOD, META_WIDTH = 0) extends uvm_mi::sequence_slave_sim#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_speed_meter::sequence_mi #(DATA_WIDTH, ADDR_WIDTH, CLK_PERIOD, META_WIDTH))

    function new (string name = "sequence_mi");
        super.new(name);
    endfunction

    // In this task you have to define how the MI transactions will look like
    virtual task create_sequence_item();
        uvm_mi::sequence_item_response #(DATA_WIDTH) rsp;
        rsp = uvm_mi::sequence_item_response #(DATA_WIDTH)::type_id::create("rsp");

        #(50*CLK_PERIOD)
        // Read ticks counter
        // Read request (Default value of BE = '1)
        //      ADDR
        read(10'h0);
        // Read max ticks counter
        read(10'h4);
        // Read bytes counter
        read(10'h8);

        // Print last three read responses
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);

        #(50*CLK_PERIOD)
        // Read ticks counter
        // Read request (Default value of BE = '1)
        //      ADDR
        read(10'h0);
        // Read max ticks counter
        read(10'h4);
        // Read bytes counter
        read(10'h8);
        // Clear counter
        // Write request (Default value of BE = '1)
        //       ADDR   DATA
        write(10'hc, 32'h1);

        // Print last three read responses
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);

    endtask

endclass

class sequence_mfb_data #(ITEM_WIDTH) extends uvm_sequence #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH));

    `uvm_object_param_utils(uvm_speed_meter::sequence_mfb_data#(ITEM_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "sequence_mfb_data");
        super.new(name);
    endfunction

    // In body you have to define how the MFB data will looks like
    task body;
        localparam header_width = 8;

        logic[ITEM_WIDTH-1 : 0]   m_data[];
        logic[header_width-1 : 0] header;

        req = uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)::type_id::create("req");

        // Send random data with specific size
        `uvm_do_with(req, {data.size == 137;  });
        `uvm_do_with(req, {data.size == 62;   });
        `uvm_do_with(req, {data.size == 74;   });
        `uvm_do_with(req, {data.size == 256;  });
        `uvm_do_with(req, {data.size == 1024; });
        `uvm_do_with(req, {data.size == 500;  });

        // Send random data with specific header
        start_item(req);
        m_data = new[136];
        std::randomize(m_data);
        // Header contains only data size
        header   = m_data.size();
        req.data = new[m_data.size()+header_width/ITEM_WIDTH];
        req.data = {header, m_data};
        finish_item(req);

        // Send specific data with specific size
        start_item(req);
        req.data = {8'h04, 8'h4c, 8'h1f, 8'hfe, 8'hf0, 8'h50, 8'h7a, 8'h02};
        finish_item(req);

        // Send specific data with specific size different way
        start_item(req);
        req.data = new[16];
        // Divide data word to ITEM_WIDTH chunks and insert them to array
        { >>{req.data}} = 'hf404f404f404f404;
        finish_item(req);
    endtask

endclass
