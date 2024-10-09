// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:  Radek Iša <isa@cesnet.cz> 

// SPDX-License-Identifier: BSD-3-Clause

class scoreboard #(REGIONS, PCIE_ENDPOINTS, DMA_PORTS, ITEM_WIDTH) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_pcie_top::scoreboard #(REGIONS, PCIE_ENDPOINTS, DMA_PORTS, ITEM_WIDTH))


    ////////////////////////
    // OLD INTERFACE
    //scoreboard_convert #(DMA_PORTS, ITEM_WIDTH) convert;

    ////////////////////////
    //NEW INTERFACE
    uvm_analysis_export#(uvm_pcie::request_header)      pcie_rq[PCIE_ENDPOINTS];
    uvm_analysis_export#(uvm_pcie::completer_header)    pcie_rc[PCIE_ENDPOINTS];
    uvm_analysis_export#(uvm_pcie::request_header)      pcie_cq[PCIE_ENDPOINTS];
    uvm_analysis_export#(uvm_pcie::completer_header)    pcie_cc[PCIE_ENDPOINTS];

    uvm_analysis_export#(uvm_dma::sequence_item_rq) dma_rq[PCIE_ENDPOINTS][DMA_PORTS];
    uvm_analysis_export#(uvm_dma::sequence_item_rc) dma_rc[PCIE_ENDPOINTS][DMA_PORTS];

    //////////////////
    //MI
    uvm_analysis_export#(uvm_mi::sequence_item_response #(32)) mi_rsp[PCIE_ENDPOINTS];
    uvm_mtc::mi_subscriber #(32, 32)                           mi_req[PCIE_ENDPOINTS];

    // MODEL
    protected model #(REGIONS, PCIE_ENDPOINTS, DMA_PORTS, ITEM_WIDTH) m_model;

    //////////////////
    //COMPARATORS
    protected uvm_common::comparer_unordered#(uvm_pcie::request_header)   pcie_rq_cmp[PCIE_ENDPOINTS];
    protected uvm_common::comparer_unordered#(uvm_pcie::completer_header) pcie_cc_cmp[PCIE_ENDPOINTS];

    protected uvm_common::comparer_ordered#(uvm_dma::sequence_item_rc)                  dma_rc_cmp[PCIE_ENDPOINTS][DMA_PORTS];
    protected uvm_common::comparer_ordered#(uvm_mi::sequence_item_request #(32, 32, 0)) mi_rq_cmp[PCIE_ENDPOINTS]; //CQ

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        for (int it = 0; it < PCIE_ENDPOINTS; it++) begin
            string i_string;
            i_string.itoa(it);
            pcie_rq[it] = new({"pcie_rq_", i_string}, this);
            pcie_cc[it] = new({"pcie_cc_", i_string}, this);

            for (int dma = 0; dma < DMA_PORTS; dma++) begin
                string dma_string;
                dma_string.itoa(dma);

                dma_rc[it][dma] = new({"dma_rc_", i_string, "_", dma_string}, this);
            end

            mi_rsp[it] = new({"mi_rsp_", i_string}, this);
            //mi_req[it] = new({"mi_req_", i_string}, this);
        end
    endfunction


    function int unsigned success();
        int unsigned ret = 1;
        ret &= m_model.success();
        for (int unsigned it = 0; it < PCIE_ENDPOINTS; it++) begin
            ret &= pcie_rq_cmp[it].success();
            ret &= pcie_cc_cmp[it].success();
            for (int unsigned jt = 0; jt < DMA_PORTS; jt++) begin
                ret &= dma_rc_cmp[it][jt].success();
            end
            ret &= mi_rq_cmp[it].success();
        end
        return ret;
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= m_model.used();
        for (int unsigned it = 0; it < PCIE_ENDPOINTS; it++) begin
            ret |= pcie_rq_cmp[it].used();
            ret |= pcie_cc_cmp[it].used();
            for (int unsigned jt = 0; jt < DMA_PORTS; jt++) begin
                ret |= dma_rc_cmp[it][jt].used();
            end
            ret |= mi_rq_cmp[it].used();
        end
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        m_model = model #(REGIONS, PCIE_ENDPOINTS, DMA_PORTS, ITEM_WIDTH)::type_id::create("m_model", this);

        for (int unsigned pcie = 0; pcie < PCIE_ENDPOINTS; pcie++) begin
            string i_string;
            i_string.itoa(pcie);

            pcie_rc[pcie] = new({"pcie_rc_", i_string}, this);
            pcie_cq[pcie] = new({"pcie_cq_", i_string}, this);

            mi_req[pcie] = uvm_mtc::mi_subscriber #(32, 32)::type_id::create({"mi_rq_", i_string}, this);

            pcie_rq_cmp[pcie] = uvm_common::comparer_unordered#(uvm_pcie::request_header)  ::type_id::create({"pcie_rq_cmp_", i_string}, this);
            pcie_cc_cmp[pcie] = uvm_common::comparer_unordered#(uvm_pcie::completer_header)::type_id::create({"pcie_cc_cmp_", i_string}, this);

            mi_rq_cmp[pcie] = uvm_common::comparer_ordered#(uvm_mi::sequence_item_request #(32, 32, 0))::type_id::create({"mi_rq_cmp", i_string}, this);
            mi_rq_cmp[pcie].model_tr_timeout_set(1ms);

            for (int unsigned dma = 0; dma < DMA_PORTS; dma++) begin
                string dma_string;
                dma_string.itoa(dma);

                dma_rq[pcie][dma]     = new({"dma_rq_", i_string, "_", dma_string}, this);
                dma_rc_cmp[pcie][dma] = uvm_common::comparer_ordered#(uvm_dma::sequence_item_rc)::type_id::create({"dma_rc_cmp_", i_string, "_", dma_string}, this);
            end
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        for (int unsigned pcie = 0; pcie < PCIE_ENDPOINTS; pcie++) begin

            pcie_rc[pcie].connect(m_model.pcie_rc[pcie]);
            pcie_cq[pcie].connect(m_model.pcie_cq[pcie]);

            m_model.pcie_cc[pcie].connect(pcie_cc_cmp[pcie].analysis_imp_model);
            m_model.pcie_rq[pcie].connect(pcie_rq_cmp[pcie].analysis_imp_model);
            pcie_cc[pcie].connect(pcie_cc_cmp[pcie].analysis_imp_dut);
            pcie_rq[pcie].connect(pcie_rq_cmp[pcie].analysis_imp_dut);

            mi_rsp[pcie].connect(m_model.mi_rsp[pcie]);
            m_model.mi_req[pcie].connect(mi_rq_cmp[pcie].analysis_imp_model);
            mi_req[pcie].port.connect(mi_rq_cmp[pcie].analysis_imp_dut);

            for (int unsigned it = 0; it < DMA_PORTS; it++) begin
                dma_rq[pcie][it].connect(m_model.dma_rq[pcie][it]);

                m_model.dma_rc[pcie][it].connect(dma_rc_cmp[pcie][it].analysis_imp_model);
                dma_rc[pcie][it].connect(dma_rc_cmp[pcie][it].analysis_imp_dut);
            end
        end
    endfunction

    virtual function void report_phase(uvm_phase phase);
        if (this.success() && this.used() == 0) begin
            `uvm_info(this.get_full_name(), "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------", UVM_NONE)
        end else begin
            string msg;

            msg = $sformatf("\n\tsuccess %0d used %0d", this.success(), this.used());
            `uvm_info(this.get_full_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------"}, UVM_NONE)
        end

    endfunction
endclass

