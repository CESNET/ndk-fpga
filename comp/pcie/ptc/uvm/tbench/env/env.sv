//-- env.sv: Verification environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Environment for functional verification of encode.
// This environment containts two mii agents.
class env #(DMA_MFB_UP_REGIONS, MFB_UP_REGIONS, MFB_UP_REG_SIZE,
            MFB_UP_BLOCK_SIZE, MFB_UP_ITEM_WIDTH, MFB_DOWN_REGIONS,
            DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE,
            MFB_DOWN_ITEM_WIDTH, PCIE_UPHDR_WIDTH, PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH, DMA_MVB_UP_ITEMS,
            DMA_MVB_DOWN_ITEMS, RQ_TUSER_WIDTH, RC_TUSER_WIDTH, RQ_TDATA_WIDTH, RC_TDATA_WIDTH, META_WIDTH, DMA_PORTS, ENDPOINT_TYPE, RCB_SIZE, CLK_PERIOD, DEVICE) extends uvm_env;

    `uvm_component_param_utils(uvm_ptc::env #(DMA_MFB_UP_REGIONS, MFB_UP_REGIONS, MFB_UP_REG_SIZE,
                                              MFB_UP_BLOCK_SIZE, MFB_UP_ITEM_WIDTH, MFB_DOWN_REGIONS,
                                              DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE,
                                              MFB_DOWN_ITEM_WIDTH, PCIE_UPHDR_WIDTH, PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH, DMA_MVB_UP_ITEMS,
                                              DMA_MVB_DOWN_ITEMS, RQ_TUSER_WIDTH, RC_TUSER_WIDTH, RQ_TDATA_WIDTH, RC_TDATA_WIDTH, META_WIDTH, DMA_PORTS, ENDPOINT_TYPE, RCB_SIZE, CLK_PERIOD, DEVICE));

    //uvm_reset::agent m_reset;
    //uvm_reset::agent m_reset_1;
    uvm_ptc_info::sync_tag tag_sync[DMA_PORTS];
    // UPSTREAM
    uvm_dma_up::env              #(DMA_MVB_UP_ITEMS, DMA_MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, MFB_UP_ITEM_WIDTH, DMA_PORTS) m_env_up[DMA_PORTS];
    uvm_logic_vector_array_mfb::env_tx   #(MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, 32, 0)                                      m_env_rq_mfb;
    uvm_logic_vector_mvb::env_tx #(MFB_UP_REGIONS, PCIE_UPHDR_WIDTH)                                                                       m_env_rq_mvb;
    uvm_logic_vector_mvb::env_tx #(MFB_UP_REGIONS, PCIE_PREFIX_WIDTH)                                                                      m_env_rq_prefix_mvb;
    uvm_logic_vector_array_axi::env_tx #(RQ_TDATA_WIDTH, RQ_TUSER_WIDTH, 32, MFB_UP_REGIONS, MFB_UP_BLOCK_SIZE, 1)                         m_env_rq_axi;
    // DOWNSTREAM
    uvm_logic_vector_array_mfb::env_tx   #(DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, 0)           m_env_down_mfb[DMA_PORTS];
    uvm_logic_vector_mvb::env_tx #(DMA_MVB_DOWN_ITEMS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)                                                 m_env_down_mvb[DMA_PORTS];

    uvm_pcie_rc::env #(MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, PCIE_UPHDR_WIDTH, PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH, RC_TDATA_WIDTH, RC_TUSER_WIDTH, RQ_TUSER_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE) m_env_rc;

    scoreboard #(META_WIDTH, MFB_DOWN_REGIONS, MFB_UP_REGIONS, DMA_MVB_UP_ITEMS, PCIE_PREFIX_WIDTH, PCIE_UPHDR_WIDTH, RQ_TUSER_WIDTH, DMA_MVB_DOWN_ITEMS, PCIE_DOWNHDR_WIDTH, DMA_PORTS, ENDPOINT_TYPE, DEVICE) sc;
    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Create base components of environment.
    function void build_phase(uvm_phase phase);

        //uvm_reset::config_item     m_config_reset;
        //uvm_reset::config_item     m_config_reset_1;
        // UPSTREAM
        uvm_dma_up::config_item #(DMA_PORTS)    m_config_up[DMA_PORTS];
        uvm_logic_vector_array_mfb::config_item m_config_rq_mfb;
        uvm_logic_vector_mvb::config_item       m_config_rq_mvb;
        uvm_logic_vector_mvb::config_item       m_config_rq_prefix_mvb;
        uvm_logic_vector_array_axi::config_item m_config_rq_axi;
        // DOWNSTREAM
        uvm_logic_vector_array_mfb::config_item m_config_down_mfb[DMA_PORTS];
        uvm_logic_vector_mvb::config_item       m_config_down_mvb[DMA_PORTS];
        uvm_pcie_rc::config_item                m_config_rc;


        string dma_port;
        dma_port.itoa(DMA_PORTS+1);
        // RC ENVIRONMENT
        m_config_rc                         = new;
        m_config_rc.active                  = UVM_ACTIVE;
        m_config_rc.interface_name_mfb      = "vif_rc_mfb";
        m_config_rc.interface_name_mvb      = "vif_rc_mvb";
        m_config_rc.interface_name_mvb_pref = "vif_rc_prefix_mvb";
        m_config_rc.interface_name_axi      = "vif_rc";

        uvm_config_db #(uvm_pcie_rc::config_item)::set(this, "m_env_rc", "m_config", m_config_rc);
        m_env_rc = uvm_pcie_rc::env #(MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, PCIE_UPHDR_WIDTH, PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH, RC_TDATA_WIDTH, RC_TUSER_WIDTH, RQ_TUSER_WIDTH, RCB_SIZE, CLK_PERIOD, DEVICE)::type_id::create("m_env_rc", this);

        ///////////////
        // RESETS
        //m_config_reset = new;
        //m_config_reset.active = UVM_ACTIVE;
        //m_config_reset.interface_name = "RESET_USER_X1";
        //uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_config_reset);
        //m_reset    = uvm_reset::agent::type_id::create("m_reset", this);

        //m_config_reset_1 = new;
        //m_config_reset_1.active = UVM_ACTIVE;
        //m_config_reset_1.interface_name = "RESET_USER_X2";
        //uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset_1", "m_config", m_config_reset_1);
        //m_reset_1    = uvm_reset::agent::type_id::create("m_reset_1", this);

        // RQ ENVIRONMENT
        m_config_rq_mfb                       = new;
        m_config_rq_mfb.active                = UVM_ACTIVE;
        m_config_rq_mfb.interface_name        = "vif_rq_mfb";

        m_config_rq_mvb                       = new;
        m_config_rq_mvb.active                = UVM_PASSIVE;
        m_config_rq_mvb.interface_name        = "vif_rq_mvb";

        m_config_rq_prefix_mvb                = new;
        m_config_rq_prefix_mvb.active         = UVM_PASSIVE;
        m_config_rq_prefix_mvb.interface_name = "vif_rq_prefix_mvb";

        m_config_rq_axi                       = new;
        m_config_rq_axi.active                = UVM_ACTIVE;
        m_config_rq_axi.interface_name        = "vif_rq";
        m_config_rq_axi.meta_behav            = uvm_logic_vector_array_axi::config_item::META_EOF;


        uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, "m_env_rq_mfb", "m_config", m_config_rq_mfb);
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_rq_mvb", "m_config", m_config_rq_mvb);
        uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_rq_prefix_mvb", "m_config", m_config_rq_prefix_mvb);
        uvm_config_db #(uvm_logic_vector_array_axi::config_item)::set(this, "m_env_rq_axi", "m_config", m_config_rq_axi);

        m_env_rq_mfb        = uvm_logic_vector_array_mfb::env_tx   #(MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, 32, 0)::type_id::create("m_env_rq_mfb", this);
        m_env_rq_mvb        = uvm_logic_vector_mvb::env_tx #(MFB_UP_REGIONS, PCIE_UPHDR_WIDTH)::type_id::create("m_env_rq_mvb", this);
        m_env_rq_prefix_mvb = uvm_logic_vector_mvb::env_tx #(MFB_UP_REGIONS, PCIE_PREFIX_WIDTH)::type_id::create("m_env_rq_prefix_mvb", this);
        m_env_rq_axi        = uvm_logic_vector_array_axi::env_tx#(RQ_TDATA_WIDTH, RQ_TUSER_WIDTH, 32, MFB_UP_REGIONS, MFB_UP_BLOCK_SIZE, 1)::type_id::create("m_env_rq_axi", this);

        //m_config_reset = new;
        //for (int i = 0; i < (DMA_PORTS+1); i++)  begin
        //    string i_string;
        //    i_string.itoa(i);
//
        //    m_config_reset.active[i] = UVM_ACTIVE;
        //    m_config_reset.interface_name[i] = {"vif_reset_", i_string};
        //end
        //uvm_config_db #(uvm_reset::env_config_item #(DMA_PORTS+1))::set(this, "m_reset", "m_config", m_config_reset);
        //m_reset    = uvm_reset::env #(DMA_PORTS+1)::type_id::create("m_reset", this);
        sc  = scoreboard #(META_WIDTH, MFB_DOWN_REGIONS, MFB_UP_REGIONS, DMA_MVB_UP_ITEMS, PCIE_PREFIX_WIDTH, PCIE_UPHDR_WIDTH, RQ_TUSER_WIDTH, DMA_MVB_DOWN_ITEMS, PCIE_DOWNHDR_WIDTH, DMA_PORTS, ENDPOINT_TYPE, DEVICE)::type_id::create("sc", this);

        for(int i = 0; i < DMA_PORTS; i++) begin
            string i_string;
            i_string.itoa(i);
            tag_sync[i] = uvm_ptc_info::sync_tag::type_id::create({"tag_sync_", i_string}, this);

            m_config_down_mfb[i]                = new;
            m_config_down_mfb[i].active         = UVM_ACTIVE;
            m_config_down_mfb[i].interface_name = {"vif_down_mfb_", i_string};

            m_config_down_mvb[i]                = new;
            m_config_down_mvb[i].active         = UVM_ACTIVE;
            m_config_down_mvb[i].interface_name = {"vif_down_mvb_", i_string};

/*             m_config_reset[i] = new;
            m_config_reset[i].active = UVM_ACTIVE;
            m_config_reset[i].interface_name = {"vif_reset_", i_string};
            uvm_config_db #(uvm_reset::config_item)::set(this, {"m_reset_", i_string}, "m_config", m_config_reset[i]);
            m_reset[i]    = uvm_reset::agent::type_id::create({"m_reset_", i_string}, this); */

            m_config_up[i]                    = new;
            m_config_up[i].active             = UVM_ACTIVE;
            m_config_up[i].port               = i;
            m_config_up[i].interface_name     = "vif_up";

            uvm_config_db #(uvm_logic_vector_array_mfb::config_item)::set(this, {"m_env_down_mfb_", i_string}, "m_config", m_config_down_mfb[i]);
            uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, {"m_env_down_mvb_", i_string}, "m_config", m_config_down_mvb[i]);
            uvm_config_db #(uvm_dma_up::config_item #(DMA_PORTS))::set(this, {"m_env_up_", i_string}, "m_config", m_config_up[i]);

            m_env_down_mfb[i] = uvm_logic_vector_array_mfb::env_tx #(DMA_MFB_DOWN_REGIONS, MFB_DOWN_REG_SIZE, MFB_DOWN_BLOCK_SIZE, MFB_DOWN_ITEM_WIDTH, 0)::type_id::create({"m_env_down_mfb_", i_string}, this);
            m_env_down_mvb[i] = uvm_logic_vector_mvb::env_tx       #(DMA_MVB_DOWN_ITEMS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)::type_id::create({"m_env_down_mvb_", i_string}, this);
            m_env_up[i]       = uvm_dma_up::env                    #(DMA_MVB_UP_ITEMS, DMA_MFB_UP_REGIONS, MFB_UP_REG_SIZE, MFB_UP_BLOCK_SIZE, MFB_UP_ITEM_WIDTH, DMA_PORTS)::type_id::create({"m_env_up_", i_string}, this);
        end


    endfunction

    // Connect agent's ports with ports from scoreboard.
    function void connect_phase(uvm_phase phase);

        m_env_rc.m_env_rc_prefix_mvb.analysis_port.connect(sc.rc_prefix_mvb_in);

        // m_env_rq_mvb.analysis_port.connect(m_env_rc.m_monitor.analysis_export);
        sc.rq_hdr_user_out.connect(m_env_rc.m_monitor.analysis_export);
        m_env_rq_mvb.analysis_port.connect(sc.rq_mvb_out);
        m_env_rq_prefix_mvb.analysis_port.connect(sc.rq_prefix_mvb_out);

        if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin
            m_env_rq_mfb.analysis_port_data.connect(sc.rq_mfb_out);
            m_env_rc.m_env_rc_mfb.analysis_port_data.connect(sc.rc_mfb_in);
            m_env_rc.m_env_rc_mfb.analysis_port_meta.connect(sc.rc_meta_in);
        end else begin
            m_env_rq_axi.analysis_port_data.connect(sc.rq_mfb_out);
            m_env_rq_axi.analysis_port_meta.connect(sc.rq_axi_meta_out);
            m_env_rc.m_env_rc_axi.analysis_port_data.connect(sc.rc_mfb_in);
        end

        //m_sequencer.m_reset    = m_reset.m_sequencer;

        for (int i = 0; i < DMA_PORTS; i++) begin
            m_env_down_mfb[i].analysis_port_data.connect(sc.down_mfb_out[i]);
            m_env_down_mvb[i].analysis_port.connect(sc.down_mvb_out[i]);
            m_env_up[i].m_env_up_mfb.analysis_port_data.connect(sc.up_mfb_in[i]);
            m_env_up[i].m_env_up_mvb.analysis_port.connect(sc.up_mvb_in[i]);

            //m_reset.sync_connect(m_env_up[0].reset_sync);

        end
        //m_reset.sync_connect(m_env_rq_mfb.reset_sync);
        //m_reset.sync_connect(m_env_rq_mvb.reset_sync);
    endfunction


    virtual task run_phase(uvm_phase phase);
        for (int i = 0; i < DMA_PORTS; i++) begin
            m_env_up[i].m_driver.tag_sync = tag_sync[i];
            sc.answer_compare[i].tag_sync = tag_sync[i];
        end
    endtask

endclass
