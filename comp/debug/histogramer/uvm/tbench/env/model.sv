//-- model.sv: Model of implementation
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author: Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`include "../tests/const.sv"

class model #(
    INPUT_WIDTH,
    BOX_WIDTH,
    BOX_CNT,
    READ_PRIOR,
    CLEAR_BY_READ,
    CLEAR_BY_RST,
    DEVICE,
    REQ_WIDTH,
    RESP_WIDTH,
    ADDR_WIDTH
) extends uvm_component;
    `uvm_component_param_utils(uvm_histogramer::model #(
        INPUT_WIDTH,
        BOX_WIDTH,
        BOX_CNT,
        READ_PRIOR,
        CLEAR_BY_READ,
        CLEAR_BY_RST,
        DEVICE,
        REQ_WIDTH,
        RESP_WIDTH,
        ADDR_WIDTH
    ))

    typedef logic unsigned [INPUT_WIDTH     - 1 : 0] value_t;
    typedef logic unsigned [BOX_WIDTH       - 1 : 0] box_t;
    typedef logic unsigned [$clog2(BOX_CNT) - 1 : 0] addr_t;

    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(REQ_WIDTH))    in_data;
    uvm_analysis_port #(uvm_logic_vector::sequence_item#(RESP_WIDTH))       out_data;

    box_t boxes[addr_t];

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        in_data     = new("in_data", this);
        out_data    = new("out_data", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (in_data.used()    != 0);
        return ret;
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            run_model();
        end
    endtask

    task run_model();
        uvm_logic_vector::sequence_item#(REQ_WIDTH)   tr_in_data;
        uvm_logic_vector::sequence_item#(RESP_WIDTH)  tr_out_data;

        logic   read_req;
        value_t val;
        addr_t  addr;
        box_t   box;

        in_data.get(tr_in_data);
        {read_req, val, addr} = tr_in_data.data;

        if (read_req) begin
            box = read(addr);

            tr_out_data = uvm_logic_vector::sequence_item#(RESP_WIDTH)::type_id::create("tr_out_data");
            tr_out_data.data = 0;
            tr_out_data.data = {box};
            out_data.write(tr_out_data);
        end else begin
            new_val(val);
        end
    endtask

    function void new_val(value_t val);
        addr_t addr = val >> (INPUT_WIDTH - $clog2(BOX_CNT));

        //$write("New val %d (addr %d)\n", val, addr);

        if ( ! boxes.exists(addr)) begin
            boxes[addr] = 0;
        end

        // Handle box overflow
        if (boxes[addr] != 2 ** BOX_WIDTH - 1) begin
            boxes[addr] ++;
        end
    endfunction

    function box_t read(addr_t addr);
        box_t box = 0;

        if (boxes.exists(addr)) begin
            box = boxes[addr];
        end

        if (CLEAR_BY_READ) begin

            boxes[addr] = 0;

        end
        //$write("Read addr %d, box %d\n", addr, box);
        return box;
    endfunction

endclass
