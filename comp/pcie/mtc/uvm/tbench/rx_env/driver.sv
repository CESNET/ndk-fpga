//-- driver.sv
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class driver#(MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE) extends uvm_component;
    `uvm_component_param_utils(uvm_pcie_cq::driver#(MFB_ITEM_WIDTH, DEVICE, ENDPOINT_TYPE))

    uvm_seq_item_pull_port #(uvm_pcie_hdr::sequence_item) seq_item_port_pcie_hdr;
    mailbox#(uvm_pcie_hdr::sequence_item)                 logic_vector_export;
    mailbox#(uvm_pcie_hdr::sequence_item)                 pcie_hdr_rw_export;
    uvm_pcie_hdr::sync_tag                                tag_sync;

    protected int unsigned tr_cnt = 0;
    protected int unsigned mi_cnt = 0;

    localparam IS_INTEL_DEV    = (DEVICE == "STRATIX10" || DEVICE == "AGILEX");
    localparam IS_MFB_META_DEV = (ENDPOINT_TYPE == "P_TILE" || ENDPOINT_TYPE == "R_TILE") && IS_INTEL_DEV;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
        seq_item_port_pcie_hdr  = new("seq_item_port_pcie_hdr", this);

        logic_vector_export       = new(1);
        pcie_hdr_rw_export       = new(1);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
       void'(tag_sync.fill_array());

       forever begin
            string          msg = "";
            uvm_pcie_hdr::msg_type rw;
            uvm_pcie_hdr::sequence_item  cq_header_req;
            uvm_pcie_hdr::sequence_item  cq_header_req_cloned;

            seq_item_port_pcie_hdr.get_next_item(cq_header_req);

            rw = uvm_pcie_hdr::encode_type(cq_header_req.req_type, IS_INTEL_DEV);
            if (rw == uvm_pcie_hdr::TYPE_READ || rw == uvm_pcie_hdr::TYPE_ERR) begin
                while (!(tag_sync.list_of_tags.exists(cq_header_req.tag))) begin
                    #(10ns*$urandom_range(1, 100));
                end

                tag_sync.remove_element(cq_header_req.tag);
            end

            tr_cnt++;

            $cast(cq_header_req_cloned, cq_header_req.clone());
            pcie_hdr_rw_export.put(cq_header_req_cloned);
            logic_vector_export.put(cq_header_req_cloned);

            seq_item_port_pcie_hdr.item_done();
        end
    endtask

endclass

