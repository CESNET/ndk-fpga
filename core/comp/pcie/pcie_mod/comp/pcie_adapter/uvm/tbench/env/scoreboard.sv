//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class scoreboard extends uvm_scoreboard;

    `uvm_component_param_utils(uvm_pcie_adapter::scoreboard)

    uvm_common::comparer_ordered#(uvm_pcie::header) m_pcie_cc;
    uvm_common::comparer_ordered#(uvm_pcie::header) m_pcie_rq;

    uvm_common::comparer_ordered#(uvm_pcie::header) m_mfb_rc;
    uvm_common::comparer_ordered#(uvm_pcie::header) m_mfb_cq;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;

        ret |= m_pcie_cc.used();
        ret |= m_pcie_rq.used();
        ret |= m_mfb_rc .used();
        ret |= m_mfb_cq .used();
        return ret;
    endfunction

    function int unsigned errors();
        int unsigned ret = 0;

        ret |= m_pcie_cc.errors != 0;
        ret |= m_pcie_rq.errors != 0;
        ret |= m_mfb_rc .errors != 0;
        ret |= m_mfb_cq .errors != 0;
        return ret;
    endfunction

    function string compared();
        string ret = "\n";

        //$swrite(ret, "%s\tMFB RC DATA COMPARED: %0d\n", ret, mfb_rc_data_cmp.compared);
        //$swrite(ret, "%s\tMFB CQ DATA COMPARED: %0d\n", ret, mfb_cq_data_cmp.compared);
        //if (IS_INTEL_DEV) begin
        //    $swrite(ret, "%s\tMFB RC META COMPARED: %0d\n", ret, mfb_rc_meta_cmp.compared);
        //    $swrite(ret, "%s\tMFB CQ META COMPARED: %0d\n", ret, mfb_cq_meta_cmp.compared);
        //    $swrite(ret, "%s\tAVST UP DATA COMPARED: %0d\n", ret, avst_up_data_cmp.compared);
        //    $swrite(ret, "%s\tAVST UP META COMPARED: %0d\n", ret, avst_up_meta_cmp.compared);
        //end else begin
        //    $swrite(ret, "%s\tAXI CC DATA COMPARED: %0d\n", ret, axi_cc_data_cmp.compared);
        //    $swrite(ret, "%s\tAXI RQ DATA COMPARED: %0d\n", ret, axi_rq_data_cmp.compared);
        //end

        return ret;
    endfunction

    function string get_errors();
        string ret = "\n";

        //$swrite(ret, "%s\tMFB RC DATA ERRORS: %0d\n", ret, mfb_rc_data_cmp.errors);
        //$swrite(ret, "%s\tMFB CQ DATA ERRORS: %0d\n", ret, mfb_cq_data_cmp.errors);
        //if (IS_INTEL_DEV) begin
        //    $swrite(ret, "%s\tMFB RC META ERRORS: %0d\n", ret, mfb_rc_meta_cmp.errors);
        //    $swrite(ret, "%s\tMFB CQ META ERRORS: %0d\n", ret, mfb_cq_meta_cmp.errors);
        //    $swrite(ret, "%s\tAVST UP DATA ERRORS: %0d\n", ret, avst_up_data_cmp.errors);
        //    $swrite(ret, "%s\tAVST UP META ERRORS: %0d\n", ret, avst_up_meta_cmp.errors);
        //end else begin
        //    $swrite(ret, "%s\tAXI CC DATA ERRORS: %0d\n", ret, axi_cc_data_cmp.errors);
        //    $swrite(ret, "%s\tAXI RQ DATA ERRORS: %0d\n", ret, axi_rq_data_cmp.errors);
        //end

        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        m_pcie_cc = uvm_common::comparer_ordered#(uvm_pcie::header)::type_id::create("m_pcie_cc",this);
        m_pcie_rq = uvm_common::comparer_ordered#(uvm_pcie::header)::type_id::create("m_pcie_rq",this);
        m_mfb_rc  = uvm_common::comparer_ordered#(uvm_pcie::header)::type_id::create("m_mfb_rc",this);
        m_mfb_cq  = uvm_common::comparer_ordered#(uvm_pcie::header)::type_id::create("m_mfb_cq",this);
    endfunction

    function void connect_phase(uvm_phase phase);
        //Sometime dut can be quicker that model. Allow some delay to model.
        // TODO: FIX in scoreboard. Timeout use time when first part of packet
        // received to monitor.
        m_pcie_cc.model_tr_timeout_set(100ns);
        m_pcie_rq.model_tr_timeout_set(100ns);
        m_mfb_rc.model_tr_timeout_set(100ns);
        m_mfb_cq.model_tr_timeout_set(100ns);
    endfunction

    virtual function void report_phase(uvm_phase phase);
        string msg = "\n";
        //$swrite(msg, "%s-------------------------------------------------------------------\n", msg);
        //$swrite(msg, "%s                           STATISTICS:                             \n", msg);
        //$swrite(msg, "%s-------------------------------------------------------------------\n", msg);
        //$swrite(msg, "%s%s\n%s \n", msg, this.compared(), this.get_errors());
        //$swrite(msg, "%s-------------------------------------------------------------------\n", msg);
        //$swrite(msg, "%s-------------------------------------------------------------------\n", msg);

        if (this.used() == 0 && this.errors() == 0) begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------", msg), UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------", msg), UVM_NONE)
        end

    endfunction

endclass
