//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class compare_data extends uvm_common::comparer_base_ordered#(uvm_pcie::header, uvm_logic_vector_array::sequence_item#(32));
    `uvm_component_utils(uvm_cq_mfb2axi::compare_data)

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(uvm_pcie::header tr_model, uvm_logic_vector_array::sequence_item#(32) tr_dut);
        logic[32-1:0] hdr_data[4];
        logic[32-1:0] cmp_data[];
        int unsigned ret = 1;
        uvm_pcie::request_header cq_hdr;

        if ($cast(cq_hdr, tr_model)) begin
            uvm_pcie_axi::hdr_cq_set(hdr_data, cq_hdr, 0, null, 26);
            cmp_data = {hdr_data, tr_model.data};
            ret &= (cmp_data === tr_dut.data);
        end else begin
            `uvm_fatal(this.get_full_name(), $sformatf("\n\tWrong type of header expecting request header\n\t%s", tr_model.convert2string()));
            ret = 0;
        end
        return ret;
    endfunction
endclass

class compare_tlp extends uvm_common::comparer_base_ordered#(uvm_pcie::header, uvm_logic_vector::sequence_item#(32));
    `uvm_component_utils(uvm_cq_mfb2axi::compare_tlp)

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(uvm_pcie::header tr_model, uvm_logic_vector::sequence_item#(32) tr_dut);
        int unsigned ret = 1;
        `uvm_fatal(this.get_full_name(), "\n\tNOT IMPLEMENTED");
        return ret;
    endfunction
endclass


class scoreboard extends uvm_scoreboard;

    `uvm_component_utils(uvm_cq_mfb2axi::scoreboard)
    // Analysis components.
    compare_data cmp_data;
    compare_tlp  cmp_tlp;

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= cmp_data.used();
        ret |= cmp_tlp.used();
        return ret;
    endfunction

    function int unsigned success();
        int unsigned ret = 1;
        ret &= cmp_data.success();
        ret &= cmp_tlp.success();
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        cmp_data = compare_data::type_id::create("cmp_data", this);
        cmp_tlp  = compare_tlp::type_id::create("cmp_tlp", this);
    endfunction

    function void connect_phase(uvm_phase phase);
    endfunction

    virtual function void report_phase(uvm_phase phase);
        string msg = "\n";
        msg = {msg, $sformatf("\tCompared/errors: %0d/%0d\n",  cmp_data.compared, cmp_data.errors)};

        if (this.used() == 0 && this.success() == 1) begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------", msg), UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), $sformatf("%s\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------", msg), UVM_NONE)
        end

    endfunction

endclass
