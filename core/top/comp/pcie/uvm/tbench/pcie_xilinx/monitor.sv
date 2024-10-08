// monitor.sv: pcie monitor 
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class monitor extends uvm_pcie::monitor;
    `uvm_component_param_utils(uvm_pcie_xilinx::monitor);

    localparam ITEM_WIDTH = 32;
    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) axi_cq;
    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) axi_cc;
    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) axi_rq;
    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) axi_rc;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        axi_cq = new("axi_cq", this);
        axi_cc = new("axi_cc", this);
        axi_rq = new("axi_rq", this);
        axi_rc = new("axi_rc", this);
    endfunction

    task run_cq();
        forever begin
            uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data;
            uvm_pcie_extend::request_header pcie_cq;
            logic [2-1:0]  at;
            logic [64-1:2] address;
            logic [11-1:0] length;
            logic [4-1:0]  req_type;
            logic [16-1:0] requester_id;
            logic [8-1:0]  tag;
            logic [8-1:0]  target_function;
            logic [9-1:0]  bar;
            logic [3-1:0]  tc;
            logic [3-1:0]  attr;
            logic [1-1:0]  r0;
            logic [1-1:0]  r1;

            axi_cq.get(data);

             {r1, attr, tc, bar, target_function, tag, requester_id, r0, req_type, length, address, at} = { data.data[3], data.data[2], data.data[1], data.data[0]};
             pcie_cq = uvm_pcie_extend::request_header::type_id::create("pcie_cq", this);


             case(req_type)
                4'b0000 : {pcie_cq.fmt, pcie_cq.pcie_type} = {2'b00, address[64-1:32] != 32'b0 ? 1'b1 : 1'b0, 5'b00000};
                4'b0001 : {pcie_cq.fmt, pcie_cq.pcie_type} = {2'b01, address[64-1:32] != 32'b0 ? 1'b1 : 1'b0, 5'b00000};
                default : {pcie_cq.fmt, pcie_cq.pcie_type} = {2'b00, address[64-1:32] != 32'b0 ? 1'b1 : 1'b0, 1'b0 ,req_type};
            endcase

            pcie_cq.traffic_class     = tc;
            pcie_cq.id_based_ordering = attr[2];
            pcie_cq.relaxed_ordering  = attr[1];
            pcie_cq.no_snoop          = attr[0];
            pcie_cq.th                = 0;
            pcie_cq.td                = 0;
            pcie_cq.ep                = 0;
            pcie_cq.at                = at;
            pcie_cq.length            = length;
            pcie_cq.requester_id      = requester_id;
            pcie_cq.tag               = tag;
            pcie_cq.fbe               = 4'b1111;
            pcie_cq.lbe               = (length != 1) ? 4'b1111 : 0;
            pcie_cq.address           = address;
            pcie_cq.ph                = 0;
            pcie_cq.bar               = bar[2:0];
            pcie_cq.bar_aperture      = bar[9-1:3];
            pcie_cq.vf                = target_function;
            pcie_cq.data      = new[data.data.size() - 4];
            for (int it = 0; it < data.data.size()-4; it++) begin
                pcie_cq.data[it] = data.data[4+it];
            end

            cq_analysis_port.write(pcie_cq);
        end
    endtask


    task run_cc();
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data;
        forever begin
            uvm_pcie::completer_header pcie_cc;
            axi_cc.get(data);

            pcie_cc = get_comp_hdr(data, this);
            cc_analysis_port.write(pcie_cc);
        end
    endtask

    task run_rq();
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data;
        forever begin
            uvm_pcie::request_header pcie_rq;
            axi_rq.get(data);

            pcie_rq = get_rq_hdr(data, this);
            rq_analysis_port.write(pcie_rq);
        end
    endtask

    task run_rc();
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data;
        forever begin
            uvm_pcie::completer_header pcie_rc;
            axi_rc.get(data);

            pcie_rc = get_comp_hdr(data, this);
            rc_analysis_port.write(pcie_rc);
        end
    endtask

    task run_phase(uvm_phase phase);
        fork
            run_cq();
            run_cc();
            run_rq();
            run_rc();
        join
    endtask

endclass

