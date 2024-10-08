// model_base.sv: Model of pcie top
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause 


class model #(REGIONS, PCIE_ENDPOINTS, DMA_PORTS, ITEM_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_pcie_top::model#(REGIONS, PCIE_ENDPOINTS, DMA_PORTS, ITEM_WIDTH))

    // Remove this shit
    localparam DEVICE        = "ULTRASCALE";
    localparam ENDPOINT_TYPE = "DUMMY";

    //PCIE
    uvm_analysis_export  #(uvm_pcie::request_header)   pcie_rq[PCIE_ENDPOINTS];
    uvm_analysis_export  #(uvm_pcie::completer_header) pcie_rc[PCIE_ENDPOINTS];
    uvm_analysis_export  #(uvm_pcie::request_header)   pcie_cq[PCIE_ENDPOINTS];
    uvm_analysis_export  #(uvm_pcie::completer_header) pcie_cc[PCIE_ENDPOINTS];

    uvm_analysis_export  #(uvm_dma::sequence_item_rq) dma_rq[PCIE_ENDPOINTS][DMA_PORTS];
    uvm_analysis_export  #(uvm_dma::sequence_item_rc) dma_rc[PCIE_ENDPOINTS][DMA_PORTS];

    ////
    //MI
    uvm_analysis_export #(uvm_mi::sequence_item_response #(32))        mi_rsp[PCIE_ENDPOINTS];
    uvm_analysis_export #(uvm_mi::sequence_item_request #(32, 32, 0))  mi_req[PCIE_ENDPOINTS];

    protected model_mtc #(32, 32)                        mtc[PCIE_ENDPOINTS];
    protected model_ptc#(REGIONS, DMA_PORTS, ITEM_WIDTH) ptc[PCIE_ENDPOINTS];

    function new(string name = "model_base", uvm_component parent = null);
        super.new(name, parent);

        for (int unsigned pcie = 0; pcie < PCIE_ENDPOINTS; pcie++) begin
            string pcie_str = $sformatf("_%0d", pcie);

            pcie_rq[pcie] = new({"pcie_rq", pcie_str}, this);
            pcie_rc[pcie] = new({"pcie_rc", pcie_str}, this);
            pcie_cq[pcie] = new({"pcie_cq", pcie_str}, this);
            pcie_cc[pcie] = new({"pcie_cc", pcie_str}, this);

            for (int dma = 0; dma < DMA_PORTS; dma++) begin
                string dma_str = {pcie_str, $sformatf("_%d", dma)};

                dma_rq[pcie][dma] = new({"dma_rq", dma_str}, this);
                dma_rc[pcie][dma] = new({"dma_rc", dma_str}, this);
            end

            mi_rsp[pcie] = new({"mi_rsp", pcie_str}, this);
            mi_req[pcie] = new({"mi_req", pcie_str}, this);
        end
    endfunction

    function int unsigned success();
        int unsigned ret = 1;
        for (int unsigned it = 0; it < PCIE_ENDPOINTS; it++) begin
            ret &= mtc[it].success();
            ret &= ptc[it].success();
        end
        return ret;
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        for (int unsigned it = 0; it < PCIE_ENDPOINTS; it++) begin
            ret |= mtc[it].used();
            ret |= ptc[it].used();
        end
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        for (int unsigned it = 0; it < PCIE_ENDPOINTS; it++) begin
            const string pcie_str = $sformatf("_%0d", it);
            model_ptc_config ptc_cfg;

            mtc[it] = model_mtc #(32, 32)::type_id::create({"mtc", pcie_str}, this);

            ptc_cfg = new();
            ptc_cfg.path = $sformatf("testbench.DUT_U.VHDL_DUT_U.pcie_ctrl_g[%0d].pcie_ctrl_i.ptc_g.ptc_i", it);
            uvm_config_db #(model_ptc_config)::set(this, {"ptc", pcie_str}, "m_config", ptc_cfg);
            ptc[it] = model_ptc#(REGIONS, DMA_PORTS, ITEM_WIDTH)::type_id::create({"ptc", pcie_str}, this);
        end
    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);
        //connet IN/OUT
        for (int unsigned pcie = 0; pcie < PCIE_ENDPOINTS; pcie++) begin
            ptc[pcie].pcie_rq.connect(pcie_rq[pcie]);
            pcie_rc[pcie].connect(ptc[pcie].pcie_rc.analysis_export);

            for (int unsigned dma = 0; dma < DMA_PORTS; dma++) begin
                ptc[pcie].dma_rc[dma].connect(dma_rc[pcie][dma]);
                dma_rq[pcie][dma].connect(ptc[pcie].dma_rq[dma].analysis_export);
            end

            //MTC
            mtc[pcie].pcie_cc.connect(pcie_cc[pcie]);
            pcie_cq[pcie].connect(mtc[pcie].pcie_cq.analysis_export);
            mi_rsp[pcie].connect(mtc[pcie].mi_rsp.analysis_export);
            mtc[pcie].mi_req.connect(mi_req[pcie]);
        end
    endfunction

endclass


