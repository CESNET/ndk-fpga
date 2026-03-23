//-- test.sv: Verification test
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class speed #(
    int unsigned USR_MFB_REGIONS,
    int unsigned USR_MFB_REGION_SIZE,
    int unsigned USR_MFB_BLOCK_SIZE,
    int unsigned USR_MFB_ITEM_WIDTH,
    int unsigned PCIE_RQ_REGIONS,
    int unsigned PCIE_RQ_REGION_SIZE,
    int unsigned PCIE_RQ_BLOCK_SIZE,
    int unsigned PCIE_RQ_ITEM_WIDTH,
    int unsigned CHANNELS,
    int unsigned PKT_SIZE_MAX,
    int unsigned MI_WIDTH,
    string DEVICE,
    int unsigned POINTER_WIDTH,
    int unsigned SW_ADDR_WIDTH
) extends base #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS,
                 PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, CHANNELS,
                 PKT_SIZE_MAX, MI_WIDTH, DEVICE, POINTER_WIDTH, SW_ADDR_WIDTH);

    typedef uvm_component_registry #(test::speed #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE,
                                                   USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE,
                                                   PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH,
                                                   CHANNELS, PKT_SIZE_MAX, MI_WIDTH, DEVICE, POINTER_WIDTH,
                                                   SW_ADDR_WIDTH), "test::speed") type_id;

    uvm_dma_ll::env #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS,
                      PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, CHANNELS,
                      PKT_SIZE_MAX, MI_WIDTH, DEVICE, POINTER_WIDTH, SW_ADDR_WIDTH) m_env;

    localparam USR_MFB_META_WIDTH = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);

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
        uvm_logic_vector_array_mfb::sequence_lib_rx #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, USR_MFB_META_WIDTH)::type_id::set_inst_override(
            uvm_logic_vector_array_mfb::sequence_lib_rx_speed #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, USR_MFB_META_WIDTH)::get_type(),
            "m_env.m_env_rx.*", this
        );

        uvm_mfb::sequence_lib_tx #(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_RQ_META_WIDTH)::type_id::set_inst_override(
            uvm_mfb::sequence_lib_tx_speed #(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_RQ_META_WIDTH)::get_type(),
            "m_env.m_pcie_rq_mfb_env.*", this
        );

        uvm_mfb::sequence_lib_tx #(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_RQ_META_WIDTH)::type_id::set_inst_override(
            uvm_mfb::sequence_lib_tx_speed #(PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_RQ_META_WIDTH)::get_type(),
            "m_env.m_ptr_upd_mfb_env.*", this
        );

        m_env = uvm_dma_ll::env #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH,
                                  PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH,
                                  CHANNELS, PKT_SIZE_MAX, MI_WIDTH, DEVICE, POINTER_WIDTH,
                                  SW_ADDR_WIDTH)::type_id::create("m_env", this);
    endfunction
endclass
