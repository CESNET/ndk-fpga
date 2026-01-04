//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class scoreboard#(
    int unsigned DMA_PORTS
)extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_ptc::scoreboard#(DMA_PORTS))

    uvm_common::comparer_unordered #(uvm_pcie::header) pcie_rq_cmp;
    uvm_common::comparer_ordered   #(uvm_dma::sequence_item_rc) dma_rc_cmp[DMA_PORTS];

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
            dma_rc_cmp[it] = uvm_common::comparer_ordered#(uvm_dma::sequence_item_rc)::type_id::create($sformatf("dma_rc_cmp_%0d", it), this);
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
