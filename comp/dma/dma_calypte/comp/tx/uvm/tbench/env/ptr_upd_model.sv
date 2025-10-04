// ptr_upd_model.sv: Model of the Pointer updater module
// Copyright (C) 2025 MAGMIO a.s.
// Copyright (C) 2025 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
// Author(s): Vladislav Valek <vladislawalek@gmail.com>

// SPDX-License-Identifier: BSD-3-Clause

class ptr_updater_model #(POINTER_WIDTH, CHANNELS, UPD_THRESHOLD) extends uvm_component;
    `uvm_component_param_utils(uvm_tx_dma_calypte::ptr_updater_model #(POINTER_WIDTH, CHANNELS, UPD_THRESHOLD))

    localparam UPD_STOP_REQ_MVB_ITEM_W = (POINTER_WIDTH-3) + POINTER_WIDTH + 1 + 64;
    localparam RT_UPD_MVB_ITEM_W       = (POINTER_WIDTH-3) + POINTER_WIDTH + $clog2(CHANNELS);

    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(UPD_STOP_REQ_MVB_ITEM_W)) m_upd_stop_req_fifo;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #($clog2(CHANNELS)))        m_chan_start_req_fifo;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(RT_UPD_MVB_ITEM_W))       m_rt_upd_req_fifo;

    uvm_analysis_port #(uvm_pcie::request_header) m_ptr_upd_pcie_port;

    local uvm_tx_dma_calypte_regs::regmodel_top #(CHANNELS, POINTER_WIDTH) m_regmodel_top;

    typedef struct {
        logic [POINTER_WIDTH-3 -1 : 0] hhp;
        logic [POINTER_WIDTH : 0] hdp;
    } chan_info_t;

    local chan_info_t m_chan_info [CHANNELS];

    function new (string name, uvm_component parent = null);
        super.new(name, parent);

        m_upd_stop_req_fifo   = new("m_upd_stop_req_fifo", this);
        m_chan_start_req_fifo = new("m_chan_start_req_fifo", this);
        m_rt_upd_req_fifo     = new("m_rt_upd_req_fifo", this);
        m_ptr_upd_pcie_port   = new("m_ptr_upd_pcie_port", this);

        for (int unsigned it = 0; it < CHANNELS; it++) begin
            m_chan_info[it].hhp = 0;
            m_chan_info[it].hdp = 0;
        end
    endfunction

    function void regmodel_set(uvm_tx_dma_calypte_regs::regmodel_top #(CHANNELS, POINTER_WIDTH) regmodel);
        this.m_regmodel_top = regmodel;
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_upd_stop_req_fifo.used() != 0);
        ret |= (m_chan_start_req_fifo.used() != 0);
        ret |= (m_rt_upd_req_fifo.used() != 0);
        return ret;
    endfunction

    task run_phase(uvm_phase phase);
        string                                                     msg = "";
        uvm_status_e                                               status_r;
        uvm_logic_vector::sequence_item #(UPD_STOP_REQ_MVB_ITEM_W) upd_stop_req_tr;
        uvm_logic_vector::sequence_item #($clog2(CHANNELS))        chan_start_req_tr;
        uvm_logic_vector::sequence_item #(RT_UPD_MVB_ITEM_W)       rt_upd_req_tr;
        uvm_pcie::request_header                                   out_tr;

        logic [$clog2(CHANNELS)-1 : 0] chan_idx;
        logic [POINTER_WIDTH -1   : 0] hdp_int;
        logic [POINTER_WIDTH-3 -1 : 0] hhp_int;
        logic                          p2p_en_int;
        logic [63 : 0]                 upd_buff_addr_int;

        forever begin
            bit ret = 0;

            ret = m_chan_start_req_fifo.try_get(chan_start_req_tr);
            // Reset internal HHP and HDP pointer for a channel that gets started
            if (ret) begin
                chan_idx = chan_start_req_tr.data;
                m_chan_info[chan_idx].hhp = 0;
                m_chan_info[chan_idx].hdp = 0;

                msg = $sformatf("\n\t PTR_UPD_MODEL -> Channel %0d start request\n", chan_idx);
                `uvm_info(this.get_full_name(), msg,  UVM_MEDIUM);
            end

            ret = m_rt_upd_req_fifo.try_get(rt_upd_req_tr);
            if (ret) begin
                logic [POINTER_WIDTH -1 : 0] ptr_distance;
                {hhp_int, hdp_int, chan_idx} = rt_upd_req_tr.data;

                msg = "\n\t PTR_UPD_MODEL -> Runtime pointer update:\n";
                msg = {msg, $sformatf("\tChannel:      %0d\n", chan_idx)};
                msg = {msg, $sformatf("\tHHP:          %0d (%0x)\n", hhp_int, hhp_int)};
                msg = {msg, $sformatf("\tHDP:          %0d (%0x)\n", hdp_int, hdp_int)};
                msg = {msg, $sformatf("\tInternal HDP: %0d (%0x)\n", m_chan_info[chan_idx].hdp, m_chan_info[chan_idx].hdp)};

                ptr_distance = hdp_int - m_chan_info[chan_idx].hdp;
                msg = {msg, $sformatf("\tPtr distance: %0d\n", ptr_distance)};

                if (ptr_distance >= UPD_THRESHOLD) begin

                    m_chan_info[chan_idx].hhp = hhp_int;
                    m_chan_info[chan_idx].hdp = hdp_int;

                    upd_buff_addr_int = m_regmodel_top.m_regmodel_channel[chan_idx].update_base_reg.get();
                    p2p_en_int        = m_regmodel_top.m_regmodel_channel[chan_idx].exper_reg.get();

                    msg = {msg, $sformatf("\tP2P_EN: %x\n", p2p_en_int)};
                    msg = {msg, $sformatf("\tUPD_BUFF_ADDR: %x\n", upd_buff_addr_int)};

                    out_tr = uvm_pcie::request_header::type_id::create(this.get_full_name);

                    out_tr.at                = 0;
                    out_tr.traffic_class     = 0;
                    out_tr.id_based_ordering = 0;
                    out_tr.relaxed_ordering  = 0;
                    out_tr.tag               = 0;
                    out_tr.requester_id      = 0;
                    out_tr.ep                = 0;
                    out_tr.td                = 0;
                    out_tr.th                = 0;
                    out_tr.ph                = 0;
                    out_tr.no_snoop          = p2p_en_int;
                    out_tr.address           = upd_buff_addr_int[63 : 2];

                    if (upd_buff_addr_int[64-1:32] == 0) begin
                        out_tr.fmt = 3'b010;
                    end else begin
                        out_tr.fmt = 3'b011;
                    end
                    out_tr.pcie_type = 0;

                    assert(upd_buff_addr_int[2-1:0] == 0) else `uvm_fatal(this.get_full_name(), $sformatf("\n\tThis model doesnt support counting fbe. lower 2 bits of addres heve to zero"));

                    out_tr.fbe    = 4'b1111;
                    out_tr.lbe    = 4'b0011;
                    out_tr.length = 2;
                    // out_tr.data   = {{{(16-POINTER_WIDTH){1'b0}},     hdp_int},
                    //                  {{(16-(POINTER_WIDTH-3)){1'b0}}, hhp_int}};
                    out_tr.data   = {hdp_int, hhp_int};

                    m_ptr_upd_pcie_port.write(out_tr);
                    `uvm_info(this.get_full_name(), msg,  UVM_MEDIUM);
                end
            end

            ret = m_upd_stop_req_fifo.try_get(upd_stop_req_tr);
            if (ret) begin
                {hhp_int, hdp_int, p2p_en_int, upd_buff_addr_int} = upd_stop_req_tr.data;

                msg = "\n\t PTR_UPD_MODEL -> Channel stop pointer update:\n";
                msg = {msg, $sformatf("\tHHP: %0d (%0x)\n", hhp_int, hhp_int)};
                msg = {msg, $sformatf("\tHDP: %0d (%0x)\n", hdp_int, hdp_int)};
                msg = {msg, $sformatf("\tP2P_EN: %x\n", p2p_en_int)};
                msg = {msg, $sformatf("\tUPD_BUFF_ADDR: %x\n", upd_buff_addr_int)};
                `uvm_info(this.get_full_name(), msg,  UVM_MEDIUM);

                out_tr = uvm_pcie::request_header::type_id::create(this.get_full_name);

                out_tr.at                = 0;
                out_tr.traffic_class     = 0;
                out_tr.id_based_ordering = 0;
                out_tr.relaxed_ordering  = 0;
                out_tr.tag               = 0;
                out_tr.requester_id      = 0;
                out_tr.ep                = 0;
                out_tr.td                = 0;
                out_tr.th                = 0;
                out_tr.ph                = 0;
                out_tr.no_snoop          = p2p_en_int;
                out_tr.address           = upd_buff_addr_int[63 : 2];

                if (upd_buff_addr_int[64-1:32] == 0) begin
                    out_tr.fmt = 3'b010;
                end else begin
                    out_tr.fmt = 3'b011;
                end
                out_tr.pcie_type = 0;

                assert(upd_buff_addr_int[2-1:0] == 0) else `uvm_fatal(this.get_full_name(), $sformatf("\n\tThis model doesnt support counting fbe. lower 2 bits of addres heve to zero"));

                out_tr.fbe    = 4'b1111;
                out_tr.lbe    = 4'b0011;
                out_tr.length = 2;
                out_tr.data   = { hdp_int, hhp_int };

                out_tr.time_add("ptr_upd_model", $time());
                m_ptr_upd_pcie_port.write(out_tr);
            end

            #(1ns);
        end
    endtask
endclass
