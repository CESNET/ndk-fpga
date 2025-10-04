// ptr_upd_model.sv: Model of the Pointer updater module
// Copyright (C) 2025 MAGMIO a.s.
// Copyright (C) 2025 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
// Author(s): Vladislav Valek <vladislawalek@gmail.com>

// SPDX-License-Identifier: BSD-3-Clause

class ptr_updater_model #(POINTER_WIDTH, SW_ADDR_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_dma_ll::ptr_updater_model #(POINTER_WIDTH, SW_ADDR_WIDTH))

    localparam MVB_ITEM_WIDTH = 2*POINTER_WIDTH + 1 + SW_ADDR_WIDTH;

    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH)) m_ptr_upd_req_fifo;
    uvm_analysis_port #(uvm_pcie::request_header)                              m_ptr_upd_rq_mfb_port;

    function new (string name, uvm_component parent = null);
        super.new(name, parent);

        m_ptr_upd_req_fifo     = new("m_ptr_upd_req_fifo", this);
        m_ptr_upd_rq_mfb_port  = new("m_ptr_upd_rq_mfb_port", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_ptr_upd_req_fifo.used() != 0);
        return ret;
    endfunction

    task run_phase(uvm_phase phase);
        string msg = "";
        uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH) in_tr;
        uvm_pcie::request_header                          out_tr;

        logic [POINTER_WIDTH -1 : 0] hdp_int;
        logic [POINTER_WIDTH -1 : 0] hhp_int;
        logic                        p2p_en_int;
        logic [SW_ADDR_WIDTH -1 : 0] upd_buff_addr_int;

        forever begin
            // Deparse the input data
            m_ptr_upd_req_fifo.get(in_tr);
            {hhp_int, hdp_int, p2p_en_int, upd_buff_addr_int} = in_tr.data;
            msg = {msg, $sformatf("\n\t PTR_UPD_MODEL -> Received transaction:\n\t", in_tr.convert2string())};
            `uvm_info(this.get_full_name(), msg,  UVM_HIGH);

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
            out_tr.address           = { {(64-SW_ADDR_WIDTH){1'b0}}, upd_buff_addr_int[SW_ADDR_WIDTH-1:2] };

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

            m_ptr_upd_rq_mfb_port.write(out_tr);
        end
    endtask
endclass
