//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class scoreboard_dma_rc #(DMA_PORTS) extends uvm_common::comparer_ordered   #(uvm_dma::sequence_item_rc);
    `uvm_component_param_utils(uvm_ptc::scoreboard_dma_rc #(DMA_PORTS))

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // NOTE: In the newer interpretation, the unit ID is used for routing.
    // Each level is responsible for its own higher-order bits, so the unit ID
    // in a request does not need to match the unit ID in the response.
    // However, the lower-order bits must still match.
    virtual function void write_model(MODEL_ITEM tr);
        if (DMA_PORTS > 1) begin
            tr.unit_id[sv_dma_bus_pack::DMA_REQUEST_UNITID_W-1 -: $clog2(DMA_PORTS)] = 0;
        end
        super.write_model(tr);
    endfunction

    virtual function void write_dut(DUT_ITEM tr);
        if (DMA_PORTS > 1) begin
            tr.unit_id[sv_dma_bus_pack::DMA_REQUEST_UNITID_W-1 -: $clog2(DMA_PORTS)] = 0;
        end
        super.write_dut(tr);
    endfunction
endclass

class scoreboard#(
    int unsigned DMA_PORTS
)extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_ptc::scoreboard#(DMA_PORTS))

    uvm_common::comparer_unordered #(uvm_pcie::header) pcie_rq_cmp;
    scoreboard_dma_rc#(DMA_PORTS) dma_rc_cmp[DMA_PORTS];

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (pcie_rq_cmp.used()      != 0);
        for (int it = 0; it < DMA_PORTS; it++) begin
            ret |= (dma_rc_cmp[it].used() != 0);
        end
        return ret;
    endfunction

    function int unsigned success();
        int unsigned ret = 1;
        ret &= pcie_rq_cmp.success();
        for (int it = 0; it < DMA_PORTS; it++) begin
            ret &= dma_rc_cmp[it].success();
        end
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);

        pcie_rq_cmp = uvm_common::comparer_unordered #(uvm_pcie::header)::type_id::create("pcie_rq_cmp", this);
        for (int it = 0; it < DMA_PORTS; it++) begin
            dma_rc_cmp[it] = scoreboard_dma_rc#(DMA_PORTS)::type_id::create($sformatf("dma_rc_cmp_%0d", it), this);
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);
        super.run_phase(phase);
    endtask

    function void report_phase(uvm_phase phase);
        string msg = "";
        if (this.success() == 1 && this.used() == 0) begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------"}, UVM_NONE)
        end
    endfunction

endclass
