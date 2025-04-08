// model_base.sv: Model of pcie top
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class model #(REGIONS, PCIE_ENDPOINTS, DMA_PORTS, ITEM_WIDTH, DMA_BAR_ENABLE) extends uvm_component;
    `uvm_component_param_utils(uvm_pcie_top::model#(REGIONS, PCIE_ENDPOINTS, DMA_PORTS, ITEM_WIDTH, DMA_BAR_ENABLE))

    // Remove this shit
    localparam ENDPOINT_TYPE = "DUMMY";

    //PCIE
    uvm_analysis_export   #(uvm_pcie::request_header)   pcie_rq[PCIE_ENDPOINTS];
    uvm_analysis_export   #(uvm_pcie::completer_header) pcie_rc[PCIE_ENDPOINTS];
    uvm_tlm_analysis_fifo #(uvm_pcie::request_header)   pcie_cq[PCIE_ENDPOINTS];
    uvm_analysis_export   #(uvm_pcie::completer_header) pcie_cc[PCIE_ENDPOINTS];

    uvm_analysis_export   #(uvm_dma::sequence_item_rq) dma_rq[PCIE_ENDPOINTS][DMA_PORTS];
    uvm_analysis_export   #(uvm_dma::sequence_item_rc) dma_rc[PCIE_ENDPOINTS][DMA_PORTS];
    uvm_analysis_port     #(uvm_pcie::request_header)  dma_cq[PCIE_ENDPOINTS][DMA_PORTS];
    uvm_tlm_analysis_fifo #(uvm_pcie::completer_header)dma_cc[PCIE_ENDPOINTS][DMA_PORTS];

    ////
    //MI
    uvm_analysis_export #(uvm_mi::sequence_item_response #(32))        mi_rsp[PCIE_ENDPOINTS];
    uvm_analysis_export #(uvm_mi::sequence_item_request #(32, 32, 0))  mi_req[PCIE_ENDPOINTS];

    protected model_mtc #(32, 32)                        mtc[PCIE_ENDPOINTS];
    protected model_ptc#(REGIONS, DMA_PORTS, ITEM_WIDTH) ptc[PCIE_ENDPOINTS];
    protected uvm_pcie::bar_config bar_cfg;

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
                dma_cq[pcie][dma] = new({"dma_cq", dma_str}, this);
                dma_cc[pcie][dma] = new({"dma_cc", dma_str}, this);
            end

            mi_rsp[pcie] = new({"mi_rsp", pcie_str}, this);
            mi_req[pcie] = new({"mi_req", pcie_str}, this);
        end
        bar_cfg = null;
    endfunction

    virtual function void config_set(uvm_pcie::bar_config cfg);
        for (int unsigned it = 0; it < PCIE_ENDPOINTS; it++) begin
            mtc[it].bar_register(cfg);
        end
        bar_cfg = cfg;
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
            ret |= (pcie_cq[it].used() != 0);
            ret |= (mtc[it].used() != 0);
            ret |= (ptc[it].used() != 0);
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
            mi_rsp[pcie].connect(mtc[pcie].mi_rsp.analysis_export);
            mtc[pcie].mi_req.connect(mi_req[pcie]);
        end
    endfunction

    task run_pcie_cq(uvm_phase phase, int unsigned port);
        uvm_pcie::request_header request;
        forever begin
            pcie_cq[port].get(request);

            if (bar_cfg != null && request.fmt[0] == 1'b0) begin
                int unsigned bar = 0;
                uvm_pcie_extend::request_header info_item;


                assert ($cast(info_item, request)) else begin
                    `uvm_fatal(this.get_full_name(), "\n\tCannocat cat request");
                end
                bar = info_item.bar;
                if (DMA_BAR_ENABLE == 1 && bar == 2) begin
                    dma_cq[port][0].write(request);
                end else begin
                    mtc[port].pcie_cq.analysis_export.write(request);
                end
            end else begin
                mtc[port].pcie_cq.analysis_export.write(request);
            end
        end
    endtask

    task run_dma_cc(uvm_phase phase, int unsigned pcie_port, int unsigned dma_port);
        uvm_pcie::completer_header request;
        forever begin
            dma_cc[pcie_port][dma_port].get(request);
            pcie_cc[pcie_port].write(request);
        end
    endtask

    task run_phase(uvm_phase phase);
        assert(DMA_BAR_ENABLE == 0 || DMA_PORTS == 1) else begin `uvm_fatal(this.get_full_name(), "\n\t Unsupported combination when DMA_BAR_ENABLE is set then DMA_PORTS have to be one"); end
        for (int unsigned it = 0; it < PCIE_ENDPOINTS; it++) begin
            fork
                automatic int unsigned pcie_index = it;
                run_pcie_cq(phase, pcie_index);
                for (int unsigned jt = 0; jt < DMA_PORTS; jt++) begin
                    fork
                        automatic int unsigned dma_index = jt;
                        run_dma_cc(phase, pcie_index, dma_index);
                    join_none
                end
            join_none
        end
    endtask
endclass


