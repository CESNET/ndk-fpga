//-- model_base.sv: Model of implementation
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class model extends uvm_component;
    `uvm_component_param_utils(uvm_pcie_adapter::model)

    //PCIE
    uvm_tlm_analysis_fifo #(uvm_pcie::header) m_pcie_cq;
    uvm_tlm_analysis_fifo #(uvm_pcie::header) m_pcie_rc;
    uvm_analysis_port     #(uvm_pcie::header) m_pcie_cc;
    uvm_analysis_port     #(uvm_pcie::header) m_pcie_rq;

    //MFB
    uvm_tlm_analysis_fifo #(uvm_pcie::header) m_mfb_cc;
    uvm_tlm_analysis_fifo #(uvm_pcie::header) m_mfb_rq;
    uvm_analysis_port     #(uvm_pcie::header) m_mfb_rc;
    uvm_analysis_port     #(uvm_pcie::header) m_mfb_cq;


    function new(string name = "model_base", uvm_component parent = null);
        super.new(name, parent);

        m_pcie_cq = new("m_pcie_cq", this);
        m_pcie_rc = new("m_pcie_rc", this);
        m_pcie_cc = new("m_pcie_cc", this);
        m_pcie_rq = new("m_pcie_rq", this);

        m_mfb_cc  = new("m_mfb_cc", this);
        m_mfb_rq  = new("m_mfb_rq", this);
        m_mfb_rc  = new("m_mfb_rc", this);
        m_mfb_cq  = new("m_mfb_cq", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_pcie_cq.used() != 0);
        ret |= (m_pcie_rc.used() != 0);
        ret |= (m_mfb_cc.used() != 0);
        ret |= (m_mfb_rq.used() != 0);
        return ret;
    endfunction

    task run_cq();
        forever begin
            uvm_pcie::header hdr;

            m_pcie_cq.get(hdr);
            m_mfb_cq.write(hdr);
        end
    endtask

    task run_cc();
        forever begin
            uvm_pcie::header hdr;

            m_mfb_cc.get(hdr);
            m_pcie_cc.write(hdr);
        end
    endtask

    task run_rq();
        forever begin
            uvm_pcie::header hdr;

            m_mfb_rq.get(hdr);
            m_pcie_rq.write(hdr);
        end
    endtask

    task run_rc();
        forever begin
            uvm_pcie::header hdr;

            m_pcie_rc.get(hdr);
            m_mfb_rc.write(hdr);
        end
    endtask

    task run_phase(uvm_phase phase);
        fork
            run_cc();
            run_cq();
            run_rq();
            run_rc();
        join;
    endtask

endclass


