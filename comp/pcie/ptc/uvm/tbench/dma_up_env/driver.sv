//-- driver.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class driver#(DMA_PORTS) extends uvm_component;
    `uvm_component_param_utils(uvm_dma_up::driver #(DMA_PORTS))

    localparam MFB_META_WIDTH = sv_dma_bus_pack::DMA_REQUEST_LENGTH_W   + sv_dma_bus_pack::DMA_REQUEST_TYPE_W + sv_dma_bus_pack::DMA_REQUEST_FIRSTIB_W +
                                sv_dma_bus_pack::DMA_REQUEST_LASTIB_W   + sv_dma_bus_pack::DMA_REQUEST_TAG_W + sv_dma_bus_pack::DMA_REQUEST_UNITID_W   +
                                sv_dma_bus_pack::DMA_REQUEST_GLOBAL_W   + sv_dma_bus_pack::DMA_REQUEST_VFID_W + sv_dma_bus_pack::DMA_REQUEST_PASID_W   +
                                sv_dma_bus_pack::DMA_REQUEST_PASIDVLD_W + sv_dma_bus_pack::DMA_REQUEST_RELAXED_W;
    localparam PORTS_W_FIX = (DMA_PORTS > 1) ? $clog2(DMA_PORTS) : 1;

    uvm_seq_item_pull_port #(uvm_logic_vector_array::sequence_item #(32), uvm_logic_vector_array::sequence_item #(32)) seq_item_port_logic_vector_array;
    uvm_seq_item_pull_port #(uvm_ptc_info::sequence_item, uvm_ptc_info::sequence_item)     seq_item_port_info;

    mailbox #(uvm_logic_vector_array::sequence_item #(32))       logic_vector_array_export;
    mailbox #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH)) logic_vector_export;

    uvm_logic_vector_array::sequence_item #(32) frame;
    uvm_ptc_info::sequence_item                 header_req;

    uvm_logic_vector_array::sequence_item #(32)       frame_new;
    uvm_logic_vector::sequence_item #(MFB_META_WIDTH) header_new;
    logic [PORTS_W_FIX-1 : 0] port;
    int write_cnt = 0;
    int read_cnt = 0;
    uvm_ptc_info::sync_tag tag_sync;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);

        seq_item_port_logic_vector_array = new("seq_item_port_logic_vector_array", this);
        seq_item_port_info        = new("seq_item_port_info", this);
        logic_vector_array_export = new(1);
        logic_vector_export       = new(1);
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        logic [sv_dma_bus_pack::DMA_REQUEST_GLOBAL_W-1 : 0]  global_id;
        logic [sv_dma_bus_pack::DMA_REQUEST_LENGTH_W-1 : 0]  packet_size;
        logic [sv_dma_bus_pack::DMA_REQUEST_TYPE_W-1 : 0]    type_ide;
        logic [sv_dma_bus_pack::DMA_REQUEST_TAG_W-1 : 0]     tag;
        logic [sv_dma_bus_pack::DMA_REQUEST_FIRSTIB_W-1 : 0] firstib;
        logic [sv_dma_bus_pack::DMA_REQUEST_LASTIB_W-1 : 0]  lastib;
        logic [sv_dma_bus_pack::DMA_REQUEST_UNITID_W-1 : 0]  unitid;
        logic [sv_dma_bus_pack::DMA_REQUEST_VFID_W-1 : 0]    vfid;
        logic                                                pasid;
        logic                                                pasidvld;
        logic [sv_dma_bus_pack::DMA_REQUEST_RELAXED_W-1 : 0] relaxed;

        forever begin
            string debug_msg = "";
            int unsigned tag_width = 0;
            int unsigned tag_size = 0;
            // Get new sequence item to drive to interface
            seq_item_port_logic_vector_array.get_next_item(frame);
            seq_item_port_info.get_next_item(header_req);

            $cast(frame_new, frame.clone());
            header_new  = uvm_logic_vector::sequence_item #(MFB_META_WIDTH)::type_id::create("header_new");

            type_ide    = header_req.type_ide;
            firstib     = header_req.firstib;
            lastib      = header_req.lastib;

            if (DMA_PORTS > 1) begin
                header_req.tag[sv_dma_bus_pack::DMA_REQUEST_TAG_W-1 : sv_dma_bus_pack::DMA_REQUEST_TAG_W-PORTS_W_FIX] = port;
            end

            if (type_ide == 1'b0) begin
                tag_width = int'((sv_dma_bus_pack::DMA_REQUEST_TAG_W-PORTS_W_FIX));
                tag_size = 2**tag_width;
                if (tag_sync.list_of_tags.size() != tag_size) begin
                    if (DMA_PORTS > 1) begin
                        header_req.tag[sv_dma_bus_pack::DMA_REQUEST_TAG_W-1 : sv_dma_bus_pack::DMA_REQUEST_TAG_W-PORTS_W_FIX] = port;
                    end
                    if (tag_sync.list_of_tags.size() != 0) begin
                        while ((tag_sync.list_of_tags.exists(header_req.tag))) begin
                            void'(std::randomize(header_req.tag));
                            if (DMA_PORTS > 1) begin
                                header_req.tag[sv_dma_bus_pack::DMA_REQUEST_TAG_W-1 : sv_dma_bus_pack::DMA_REQUEST_TAG_W-PORTS_W_FIX] = port;
                            end
                        end
                    end
                    tag         = header_req.tag;
                    tag_sync.add_element(tag);
                end else begin
                    tag         = header_req.tag;
                    type_ide = 1'b1;
                end
            end else
                tag         = header_req.tag;

            // TODO random unitid (for each unitid is set of tags)
            // unitid      = header_req.unitid;
            unitid      = 8'b10000000;
            global_id   = header_req.global_id;
            if (DMA_PORTS > 1) begin
                vfid        = {header_req.vfid[8-1 : PORTS_W_FIX], port};
            end else begin
                vfid        = header_req.vfid;
            end
            pasid       = header_req.pasid;
            pasidvld    = header_req.pasidvld;
            relaxed     = header_req.relaxed;
            if (type_ide == 1'b1) begin
                packet_size = frame_new.data.size(); // Size in DWORDS
                write_cnt++;
            end else begin
                packet_size = header_req.length;
                read_cnt++;
            end

            header_new.data = {relaxed, pasidvld, pasid, vfid, global_id, unitid, tag, lastib, firstib, type_ide, packet_size};

            debug_msg = {debug_msg, $sformatf("\n\t =============== UP DRIVER - PORT %d =============== \n",  port)};
            if (type_ide == 1'b0) begin
                debug_msg = {debug_msg, $sformatf("\t Generated RQ MVB read request number %d: %s\n",  read_cnt, header_new.convert2string())};
            end
            if (type_ide == 1'b1) begin
                debug_msg = {debug_msg, $sformatf("\t Generated RQ MVB write request number %d: %s\n",  write_cnt, header_new.convert2string())};
                debug_msg = {debug_msg, $sformatf("\t Generated RQ write MFB: %s\n",  frame_new.convert2string())};
            end

            debug_msg = {debug_msg, $sformatf("\t Deparsed RQ MVB TR port %d:\n",  port)};

            debug_msg = {debug_msg, $sformatf("\n\t PACKET SIZE:      %0d",  packet_size)};
            debug_msg = {debug_msg, $sformatf("\n\t TAG:              0x%h",  tag)};
            debug_msg = {debug_msg, $sformatf("\n\t TYPE ID:          0x%h",  type_ide)};
            debug_msg = {debug_msg, $sformatf("\n\t RELAXED:          0x%h",  relaxed)};
            debug_msg = {debug_msg, $sformatf("\n\t PASIDVLD:         0x%h",  pasidvld)};
            debug_msg = {debug_msg, $sformatf("\n\t PASID:            0x%h",  pasid)};
            debug_msg = {debug_msg, $sformatf("\n\t VFID:             0x%h",  vfid)};
            debug_msg = {debug_msg, $sformatf("\n\t GLOBAL ID:        0x%h",  global_id)};
            debug_msg = {debug_msg, $sformatf("\n\t UNITID:           0x%h",  unitid)};
            debug_msg = {debug_msg, $sformatf("\n\t LASTIB:           0x%h\n",  lastib)};

            `uvm_info(this.get_full_name(), debug_msg ,UVM_MEDIUM);

            if (type_ide == 1'b1) begin
                logic_vector_array_export.put(frame_new);
            end
            logic_vector_export.put(header_new);

            seq_item_port_logic_vector_array.item_done();
            seq_item_port_info.item_done();
        end
    endtask

endclass

