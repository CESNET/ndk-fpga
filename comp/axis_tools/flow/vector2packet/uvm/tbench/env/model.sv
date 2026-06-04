// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>
// SPDX-License-Identifier: BSD-3-Clause

class model #(
    int unsigned RX_ITEMS,
    int unsigned RX_ITEM_WIDTH,
    int unsigned TX_ITEMS,
    int unsigned TX_ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_scoreboard;
    `uvm_component_utils(uvm_vector2packet::model #(RX_ITEMS, RX_ITEM_WIDTH, TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH))

    localparam int unsigned RX_TDATA_WIDTH = RX_ITEMS * RX_ITEM_WIDTH;
    localparam int unsigned TX_TDATA_WIDTH = TX_ITEMS * TX_ITEM_WIDTH;

    localparam int unsigned PACKETS_PER_VECTOR = (RX_TDATA_WIDTH + TX_TDATA_WIDTH - 1) / TX_TDATA_WIDTH;
    localparam int unsigned PADDED_WIDTH       = PACKETS_PER_VECTOR * TX_TDATA_WIDTH;
    localparam int unsigned PAD_BITS           = PADDED_WIDTH - RX_TDATA_WIDTH;
    localparam int unsigned VALID_BYTES = (TX_TDATA_WIDTH - PAD_BITS - 1) / 8 + 1;

    // port for input data
    uvm_tlm_analysis_fifo#(uvm_axi::sequence_item#(RX_ITEMS, RX_ITEM_WIDTH, TUSER_WIDTH)) m_rx;
    // port for output data
    uvm_analysis_port    #(uvm_axi::sequence_item#(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH)) m_tx;

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
        uvm_axi::sequence_item#(RX_ITEMS, RX_ITEM_WIDTH, TUSER_WIDTH) rx_data;
        uvm_axi::sequence_item#(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH) tx_data;

        forever begin
            //get data from input queue
            m_rx.get(rx_data);

            // process data
            if (rx_data.tvalid == 1'b1 && rx_data.tready == 1'b1) begin

                // print data when SIM_FLAGS(UVM_VERBOSITY) UVM_HIGH
                `uvm_info(
                    this.get_full_name(),$sformatf("\n\tModel get transaction%s", rx_data.convert2string()
                ), UVM_HIGH);

                for (int unsigned i = 0; i < PACKETS_PER_VECTOR; i++) begin
                    tx_data = uvm_axi::sequence_item#(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH)::type_id::create("tx_data");

                    tx_data.tuser = rx_data.tuser;
                    tx_data.tvalid = 1'b1;
                    tx_data.tready = 1'b1;

                    if (i != PACKETS_PER_VECTOR - 1) begin

                        tx_data.tdata = rx_data.tdata[i * TX_TDATA_WIDTH +: TX_TDATA_WIDTH];
                        tx_data.tkeep = '1;
                        tx_data.tlast = 1'b0;

                    end else begin

                        tx_data.tdata = rx_data.tdata[i * TX_TDATA_WIDTH +: TX_TDATA_WIDTH - PAD_BITS];
                        tx_data.tkeep = { VALID_BYTES {1'b1}};
                        tx_data.tlast = 1'b1;

                    end

                    m_tx.write(tx_data);
                end
            end
        end
    endtask
endclass
