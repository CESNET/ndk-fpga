//-- model.sv: Model of implementation
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class model #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_scoreboard;
    `uvm_component_utils(uvm_asfifox::model #(ITEMS, ITEM_WIDTH, TUSER_WIDTH))

    // port for input data
    uvm_tlm_analysis_fifo#(uvm_axi::sequence_item#(ITEMS, ITEM_WIDTH, TUSER_WIDTH)) m_rx;
    // port for output data
    uvm_analysis_port    #(uvm_axi::sequence_item#(ITEMS, ITEM_WIDTH, TUSER_WIDTH)) m_tx;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        m_rx = new("m_rx", this);
        m_tx = new("m_tx", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_rx.used() != 0);
        return ret;
    endfunction

    task run_phase(uvm_phase phase);
        uvm_axi::sequence_item#(ITEMS, ITEM_WIDTH, TUSER_WIDTH) data;

        forever begin
            //get data from input queue
            m_rx.get(data);
            // print data when SIM_FLAGS(UVM_VERBOSITY) UVM_HIGH
            `uvm_info(this.get_full_name(), $sformatf("\n\tModel get transaction%s", data.convert2string()), UVM_HIGH);
            // Process data (FIFO/ASFIFO don't change data)
            //
            if (data.tvalid == 1'b1 && data.tready == 1'b1) begin
                // send data to output port
                m_tx.write(data);
            end
        end
    endtask
endclass
