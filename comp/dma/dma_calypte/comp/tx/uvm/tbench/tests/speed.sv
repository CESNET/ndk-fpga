// speed.sv: Test for full speed on input
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


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
        uvm_logic_vector_array_mfb::sequence_lib_rx #(
            PCIE_CQ_MFB_REGIONS,
            PCIE_CQ_MFB_REGION_SIZE,
            PCIE_CQ_MFB_BLOCK_SIZE,
            PCIE_CQ_MFB_ITEM_WIDTH,
            sv_pcie_meta_pack::PCIE_CQ_META_WIDTH
        )::type_id::set_inst_override(uvm_logic_vector_array_mfb::sequence_lib_rx_speed#(
            PCIE_CQ_MFB_REGIONS,
            PCIE_CQ_MFB_REGION_SIZE,
            PCIE_CQ_MFB_BLOCK_SIZE,
            PCIE_CQ_MFB_ITEM_WIDTH,
            sv_pcie_meta_pack::PCIE_CQ_META_WIDTH
        )::get_type(), "m_env.m_cq_mfb_env.*", this);


        uvm_mfb::sequence_lib_tx #(
                USR_MFB_REGIONS,
                USR_MFB_REGION_SIZE,
                USR_MFB_BLOCK_SIZE,
                USR_MFB_ITEM_WIDTH,
                USR_MFB_META_WIDTH
        )::type_id::set_inst_override(
            uvm_mfb::sequence_lib_tx_speed #(
                USR_MFB_REGIONS,
                USR_MFB_REGION_SIZE,
                USR_MFB_BLOCK_SIZE,
                USR_MFB_ITEM_WIDTH,
                USR_MFB_META_WIDTH
            )::get_type(), "m_env.m_tx_mfb_env.*", this
        );

        uvm_mfb::sequence_lib_tx #(
                PCIE_CQ_MFB_REGIONS,
                PCIE_CQ_MFB_REGION_SIZE,
                PCIE_CQ_MFB_BLOCK_SIZE,
                PCIE_CQ_MFB_ITEM_WIDTH,
                sv_pcie_meta_pack::PCIE_RQ_META_WIDTH
            )::type_id::set_inst_override(
                uvm_mfb::sequence_lib_tx_speed #(
                    PCIE_CQ_MFB_REGIONS,
                    PCIE_CQ_MFB_REGION_SIZE,
                    PCIE_CQ_MFB_BLOCK_SIZE,
                    PCIE_CQ_MFB_ITEM_WIDTH,
                    sv_pcie_meta_pack::PCIE_RQ_META_WIDTH
                )::get_type(), "m_env.m_ptr_upd_mfb_env.*", this
        );


        super.build_phase(phase);
    endfunction

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass
