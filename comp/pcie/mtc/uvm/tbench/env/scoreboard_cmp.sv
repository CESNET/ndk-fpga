//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class mi_cmp_rq #(MI_DATA_WIDTH, type CLASS_TYPE) extends uvm_common::comparer_ordered#(CLASS_TYPE);
    `uvm_component_param_utils(uvm_mtc::mi_cmp_rq #(MI_DATA_WIDTH, CLASS_TYPE))

    uvm_analysis_port #(uvm_logic_vector::sequence_item #(MI_DATA_WIDTH)) mi_analysis_port_out;
    uvm_logic_vector::sequence_item #(MI_DATA_WIDTH)                      lv_mi_tr;
    int unsigned compared_read;
    int unsigned compared_write;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        mi_analysis_port_out = new("mi_analysis_port_out", this);
        compared_read  = 0;
        compared_write = 0;
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        int unsigned ret = 1;

        lv_mi_tr = uvm_logic_vector::sequence_item #(MI_DATA_WIDTH)::type_id::create("lv_mi_tr");
        ret = tr_model.compare(tr_dut);
        if (tr_dut.rd) begin
            lv_mi_tr.data = '1;
            mi_analysis_port_out.write(lv_mi_tr);
            compared_read++;
        end else begin
            compared_write++;
        end

        return ret;
    endfunction

    virtual function string info(logic data = 0);
        string msg ="";
        msg = $sformatf("\n\tErrors %0d Compared %0d Compared write tr %0d Compared read tr %0d Wait for tramsaction DUT(%0d) MODEL(%0d)", errors, compared, compared_write, compared_read, dut_items.size(), model_items.size());
        msg = {msg, super.info()};
        return msg;
    endfunction

    virtual function string message(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        string msg = "";
        msg = {msg, $sformatf("\n\tDUT PACKET %s\n\n",  tr_dut.convert2string())};
        msg = {msg, $sformatf("\n\tMODEL PACKET%s\n\n",  tr_model.convert2string())};
        return msg;
    endfunction

endclass

class mi_cmp_rs #(MFB_ITEM_WIDTH) extends uvm_common::comparer_base_ordered#(uvm_mtc::cc_mtc_item#(MFB_ITEM_WIDTH), uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH));
    `uvm_component_param_utils(uvm_mtc::mi_cmp_rs #(MFB_ITEM_WIDTH))

    uvm_pcie_hdr::sync_tag tag_sync;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        int unsigned ret = 1;

        if (tr_model.error == '0) begin
            ret = tr_model.data_tr.compare(tr_dut);
        end

        if ((tag_sync.list_of_tags.exists(tr_model.tag))) begin
            string msg;
            tag_sync.print_all();
            msg = {msg, $sformatf("TAG %0d EXISTS\n",  tr_model.tag)};
            msg = {msg, $sformatf("NUMBER %d\n",  compared)};
            `uvm_error(this.get_full_name(), msg);
        end
        tag_sync.add_element(tr_model.tag);

        return ret;
    endfunction

    virtual function string message(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        string msg = "";
        msg = {msg, $sformatf("\n\tDUT PACKET %s\n\n",  tr_dut.convert2string())};
        msg = {msg, $sformatf("\n\tMODEL PACKET%s\n\n",  tr_model.convert2string())};
        return msg;
    endfunction

    virtual function string info(logic data = 0);
        if (data == 1) begin
            tag_sync.print_all();
        end
        return super.info(data);
    endfunction
endclass
