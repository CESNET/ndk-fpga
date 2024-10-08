//-- sequence.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// This low level sequence define bus functionality
class byte_array_sequence#(PCIE_UPHDR_WIDTH, PCIE_DOWNHDR_WIDTH, RQ_TUSER_WIDTH, RCB_SIZE, CLK_PERIOD, string DEVICE) extends uvm_sequence #(uvm_logic_vector_array::sequence_item #(32));
    `uvm_object_utils(uvm_pcie_rc::byte_array_sequence#(PCIE_UPHDR_WIDTH, PCIE_DOWNHDR_WIDTH, RQ_TUSER_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE))

    localparam LOW_ADDR_WIDTH = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? 7 : 12; // 7 for INTEL 12 XILINX
    localparam BYTE_CNT_WIDTH = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? 12 : 13; // 12 for INTEL 13 XILINX
    localparam HDR_USER_WIDTH = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? PCIE_UPHDR_WIDTH : PCIE_UPHDR_WIDTH+RQ_TUSER_WIDTH;

    uvm_pcie_rc::tr_planner #(HDR_USER_WIDTH, RQ_TUSER_WIDTH, PCIE_DOWNHDR_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE) tr_plan;
    int unsigned mfb_cnt = 0;

    function new(string name = "sequence_simple_rx_base");
        super.new(name);
    endfunction

    task body;
        req = uvm_logic_vector_array::sequence_item #(32)::type_id::create("req");

        forever begin
            wait(tr_plan.byte_array.size() != 0);
            req = tr_plan.byte_array.pop_front();
            start_item(req);
            finish_item(req);
        end

    endtask
endclass

class logic_vector_sequence #(PCIE_DOWNHDR_WIDTH, PCIE_UPHDR_WIDTH, RQ_TUSER_WIDTH, RCB_SIZE, CLK_PERIOD, string DEVICE) extends uvm_sequence #(uvm_logic_vector::sequence_item#(PCIE_DOWNHDR_WIDTH));
    `uvm_object_param_utils(uvm_pcie_rc::logic_vector_sequence #(PCIE_DOWNHDR_WIDTH, PCIE_UPHDR_WIDTH, RQ_TUSER_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE))

    localparam LOW_ADDR_WIDTH = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? 7 : 12; // 7 for INTEL 12 XILINX
    localparam BYTE_CNT_WIDTH = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? 12 : 13; // 12 for INTEL 13 XILINX
    localparam HDR_USER_WIDTH = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? PCIE_UPHDR_WIDTH : PCIE_UPHDR_WIDTH+RQ_TUSER_WIDTH;

    uvm_pcie_rc::tr_planner #(HDR_USER_WIDTH, RQ_TUSER_WIDTH, PCIE_DOWNHDR_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE) tr_plan;
    int unsigned mvb_cnt = 0;

    function new(string name = "logic_vector_sequence");
        super.new(name);
    endfunction

    task body;
        req = uvm_logic_vector::sequence_item#(PCIE_DOWNHDR_WIDTH)::type_id::create("req");

        forever begin
            wait(tr_plan.logic_array.size() != 0);
            req = tr_plan.logic_array.pop_front();
            start_item(req);
            finish_item(req);
        end

    endtask
endclass
