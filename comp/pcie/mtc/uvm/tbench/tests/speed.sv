//-- test.sv: Verification test
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Speed variant of mi_cc_sequence: drives the MI slave without back-pressure.
// ARDY is held high (requests are accepted every cycle) and DRDY is asserted as soon as
// a read response is available, so the CQ -> MI -> CC path is not limited by the MI bus.
class mi_cc_speed #(MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_mtc::mi_cc_sequence #(MI_DATA_WIDTH, MI_ADDR_WIDTH);
    `uvm_object_param_utils(test::mi_cc_speed #(MI_DATA_WIDTH, MI_ADDR_WIDTH))

    function new(string name = "mi_cc_speed");
        super.new(name);
    endfunction

    task body;
        req = uvm_mi::sequence_item_response #(MI_DATA_WIDTH)::type_id::create("req");

        forever begin
            // No read response pending: idle beat, but still accept requests (ARDY = 1)
            if (tr_plan.mi_array.size() == 0) begin
                start_item(req);
                if(req.randomize() with {ardy == 1; drdy == 0;} == 0) begin
                    `uvm_fatal(p_sequencer.get_full_name(), "mi_cc_speed cannot randomize");
                end
                finish_item(req);
            // Read response available: send it immediately (DRDY = 1)
            end else begin
                tr_plan.mi_array.pop_front();
                start_item(req);
                if(req.randomize() with {ardy == 1; drdy == 1;} == 0) begin
                    `uvm_fatal(p_sequencer.get_full_name(), "mi_cc_speed cannot randomize");
                end
                finish_item(req);
            end

            get_response(rsp);
            save_request();
        end
    endtask
endclass

class speed extends base;
    typedef uvm_component_registry#(test::speed, "test::speed") type_id;


    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    static function type_id get_type();
        return type_id::get();
    endfunction

    function string get_type_name();
        return get_type().get_type_name();
    endfunction

    function void build_phase(uvm_phase phase);
        uvm_logic_vector_array_mfb::sequence_lib_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH,
                                                     CQ_MFB_META_WIDTH)::type_id::set_inst_override(
            uvm_logic_vector_array_mfb::sequence_lib_rx_speed
                #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, CQ_MFB_META_WIDTH)::get_type(),
            "m_env.m_env_cq.*", this
        );


        uvm_mfb::sequence_lib_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH,
                                  CC_MFB_META_WIDTH)::type_id::set_inst_override(
            uvm_mfb::sequence_lib_tx_speed
                #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, CC_MFB_META_WIDTH)::get_type(),
            "m_env.m_env_cc.*", this
        );

        uvm_mtc::mi_cc_sequence #(MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::set_type_override(
            mi_cc_speed #(MI_DATA_WIDTH, MI_ADDR_WIDTH)::get_type());

        m_env = uvm_mtc::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE,
                              MI_DATA_WIDTH, MI_ADDR_WIDTH)::type_id::create("m_env", this);
    endfunction

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass
