// driver.sv
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s):Radek Iša <isa@cesnet.cz>
//           Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class driver_data;
    logic [16-1 : 0] hdr_addr;
    logic [16-1 : 0] hdr_mask;

    logic [16-1 : 0] data_addr;
    logic [16-1 : 0] data_mask;

	// THe parameter m_chan_active_flag is to retain the send of DMA header in case a
	// channel is shut down during the send of this data. If it would not be there,
	// the DMA header would not be send and the transaction with it dropped leaving
	// the channel in an incomplete stop state.
    logic [32-1 : 0] chan_active_reg;

    int unsigned data_free_space;
    int unsigned hdr_free_space;

    function new();
        hdr_addr  = 0;
        data_addr = 0;
        chan_active_reg = 0;
    endfunction
endclass

class status_cbs extends uvm_reg_cbs;
    driver_data data;

    function new(driver_data data);
        this.data = data;
    endfunction

    virtual task pre_write(uvm_reg_item rw);
        if(rw.value[0][0] == 1'b1) begin
            data.hdr_addr  = 0;
            data.data_addr = 0;
        end
    endtask
endclass

class driver_sync #(
    int unsigned MFB_ITEM_WIDTH,
    int unsigned MFB_META_WIDTH
);

    local semaphore sem;
    mailbox #(uvm_logic_vector::sequence_item #(MFB_META_WIDTH))       pcie_meta;
    mailbox #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) pcie_data;

    function new();
        sem = new(1);
        pcie_meta = new(0);
        pcie_data = new(0);
    endfunction

    task put(int unsigned id, uvm_logic_vector::sequence_item #(MFB_META_WIDTH) meta, uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) data);
        wait(pcie_meta.num() == 0 || pcie_data.num() == 0);

        sem.get(1);
        pcie_meta.put(meta);
        pcie_data.put(data);
        sem.put(1);
    endtask
endclass

class driver #(
    string DEVICE,
    int unsigned MFB_ITEM_WIDTH,
    int unsigned CHANNELS,
    int unsigned DATA_POINTER_WIDTH,
    int unsigned PCIE_LEN_MAX
) extends uvm_driver #(sequence_item);

    `uvm_component_param_utils(uvm_tx_dma_calypte_cq::driver #(DEVICE, MFB_ITEM_WIDTH, CHANNELS, DATA_POINTER_WIDTH, PCIE_LEN_MAX))

    localparam PCIE_HDR_SIZE = 128;
    localparam DMA_HDR_SIZE  = 64;
    localparam PACKET_ALIGNMENT = 32;

    driver_sync #(MFB_ITEM_WIDTH, sv_pcie_meta_pack::PCIE_CQ_META_WIDTH) m_data_export;
    uvm_reset::sync_terminate                                            m_reset_terminate;

    local uvm_tx_dma_calypte_regs::regmodel_channel m_regmodel_channel;
    local driver_data                               m_driv_data;
    int unsigned                                    m_channel;

    typedef struct{
        uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)                  data;
        uvm_logic_vector::sequence_item #(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH) meta;
        int unsigned                                                             byte_size;
    } pcie_info;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
        m_reset_terminate = new();
    endfunction

    task status_read(output logic [32-1:0] ptr);
        uvm_status_e   status;
        uvm_reg_data_t data;
        m_regmodel_channel.status_reg.read(status, data);
        ptr = data;
    endtask

    task ptr_read(uvm_reg register, output logic [16-1:0] ptr);
        uvm_status_e   status;
        uvm_reg_data_t data;
        register.read(status, data);
        ptr = data;
    endtask

    task ptr_write(uvm_reg register, logic [16-1:0] ptr);
        uvm_status_e   status;
        uvm_reg_data_t data;

        data = ptr;
        register.write(status, data);
    endtask

    function int unsigned encode_fbe(logic [MFB_ITEM_WIDTH/8-1 : 0] be);
        int unsigned it = 0;

        if (be != 0) begin
            while (it < MFB_ITEM_WIDTH/8 && be[it] == 0) begin
                it++;
            end
        end
        return it;
    endfunction

    function int unsigned encode_lbe(logic [MFB_ITEM_WIDTH/8-1 : 0] be);
        int unsigned it  = MFB_ITEM_WIDTH/8;

        if (be != 0) begin
            while (it > 0 && be[it-1] == 0) begin
                it--;
            end;
        end
        return it;
    endfunction

    function logic[MFB_ITEM_WIDTH/8-1 : 0] decode_lbe(int unsigned mod);
        logic[MFB_ITEM_WIDTH/8-1 : 0] be = 0;

        if (mod != 0) begin
            for (int unsigned it = 0; it < mod; it++) begin
                be[it] = 1'b1;
            end
        end else begin
            be = '1;
        end
        return be;
    endfunction

    function logic [MFB_ITEM_WIDTH/8-1 : 0] lbe_to_fbe(logic [MFB_ITEM_WIDTH/8-1 : 0] lbe);
        logic [MFB_ITEM_WIDTH/8-1 : 0] fbe = 0;

        if (lbe[MFB_ITEM_WIDTH/8-1] != 1'b1) begin
            int unsigned it = MFB_ITEM_WIDTH/8;

            while (it > 0 ? (lbe[it-1] == 0) : 0) begin
                fbe[it-1] = 1'b1;
                it--;
            end
        end else begin
            fbe = '1;
        end

        return fbe;
    endfunction

    function string print_data(logic [MFB_ITEM_WIDTH-1 : 0] data[]);
        string ret = $sformatf("\nData size %0d", data.size());
        for (int unsigned it = 0; it < data.size(); it++) begin
            if (it % 8 == 0) begin
                ret = {ret, $sformatf("\n\t%h", data[it])};
            end else begin
                ret = {ret, $sformatf(" %h", data[it])};
            end
        end
        return ret;
    endfunction

    function void regmodel_set(uvm_tx_dma_calypte_regs::regmodel_channel m_regmodel);
        status_cbs cbs;

        this.m_driv_data = new();
        cbs = new(this.m_driv_data);
        this.m_regmodel_channel = m_regmodel;
        uvm_reg_field_cb::add(this.m_regmodel_channel.control_reg.dma_enable, cbs);
    endfunction

    task wait_for_free_space(int unsigned requested_space, bit is_hdr);
        logic [16-1:0] hw_ptr;
        string         debug_msg;
        int unsigned   free_space;

        debug_msg = "\n";
        debug_msg = {debug_msg, $sformatf("\twait_for_free_space method:\n")};

        if (m_driv_data.chan_active_reg != 0) begin

            debug_msg = {debug_msg, $sformatf("\tRequested space: %0d\n", requested_space)};

            if (is_hdr == 0) begin
                debug_msg = {debug_msg, $sformatf("\tInput sw address: 0x%h (%d)\n", m_driv_data.data_addr, m_driv_data.data_addr)};
                ptr_read(m_regmodel_channel.hw_data_pointer_reg, hw_ptr);
                debug_msg = {debug_msg, $sformatf("\thw_ptr in the beginning: 0x%h (%d)\n", hw_ptr, hw_ptr)};
                free_space = (hw_ptr-1 - m_driv_data.data_addr) & m_driv_data.data_mask;
            end else begin
                debug_msg = {debug_msg, $sformatf("\tInput sw address: 0x%h (%d)\n", m_driv_data.hdr_addr, m_driv_data.hdr_addr)};
                ptr_read(m_regmodel_channel.hw_hdr_pointer_reg, hw_ptr);
                debug_msg = {debug_msg, $sformatf("\thw_ptr in the beginning: 0x%h (%d)\n", hw_ptr, hw_ptr)};
                free_space = (hw_ptr-1 - m_driv_data.hdr_addr)  & m_driv_data.hdr_mask;
            end

            debug_msg = {debug_msg, $sformatf("\tFree space in the beginning: %0d\n", free_space)};

            while(free_space < requested_space) begin
                #(200ns)
                if (is_hdr == 0) begin
                    ptr_read(m_regmodel_channel.hw_data_pointer_reg, hw_ptr);
                    debug_msg = {debug_msg, $sformatf("\thw_ptr in the loop: 0x%h (%d)\n", hw_ptr, hw_ptr)};
                    free_space = (hw_ptr-1 - m_driv_data.data_addr) & m_driv_data.data_mask;
                end else begin
                    ptr_read(m_regmodel_channel.hw_hdr_pointer_reg, hw_ptr);
                    debug_msg = {debug_msg, $sformatf("\thw_ptr in the loop: 0x%h (%d)\n", hw_ptr, hw_ptr)};
                    free_space = (hw_ptr-1 - m_driv_data.hdr_addr)  & m_driv_data.hdr_mask;
                end
                debug_msg = {debug_msg, $sformatf("\tFree space in the loop: %0d\n", free_space)};
            end

            if (is_hdr == 0)
                m_driv_data.data_free_space = free_space;
            else
                m_driv_data.hdr_free_space = free_space;

        end else begin
            // If the channel is inactive, then assign the maximum free space so the packets can be send.
            if (is_hdr == 0)
                m_driv_data.data_free_space = m_driv_data.data_mask;
            else
                m_driv_data.hdr_free_space  = m_driv_data.hdr_mask;
        end

        debug_msg = {debug_msg, $sformatf("\tFree space in the end: %0d\n", free_space)};
        `uvm_info(this.get_full_name(), debug_msg, UVM_HIGH);
    endtask

    function pcie_info create_pcie_req(logic [64-1 : 0] pcie_addr, logic [11-1 : 0] pcie_len, logic [4-1:0] fbe, logic [4-1:0] lbe, logic[MFB_ITEM_WIDTH-1:0] data[], int unsigned byte_len);
        pcie_info ret;
        logic [PCIE_HDR_SIZE-1:0] pcie_hdr;

        ret.data = uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH)::type_id::create("pcie_tr.data");
        ret.meta = uvm_logic_vector::sequence_item#(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)::type_id::create("pcie_tr.meta");

        pcie_hdr = '0;
        ret.byte_size = byte_len;

        if (DEVICE == "ULTRASCALE") begin
            pcie_hdr[63 : 2]    = pcie_addr[63 : 2];
            pcie_hdr[74 : 64]   = pcie_len;
            pcie_hdr[78 : 75]   = 4'b0001; // REQ TYPE = WRITE
            pcie_hdr[114 : 112] = 3'b010; // BAR ID
            pcie_hdr[120 : 115] = 6'd26; // BAR Aperure
            ret.data.data = {pcie_hdr[31 : 0], pcie_hdr[63 : 32], pcie_hdr[95 : 64], pcie_hdr[127 : 96], data};

            ret.meta.data = '0;
            ret.meta.data[166 : 163] = fbe;
            ret.meta.data[170 : 167] = lbe;
        end else begin // Intel P/R-Tile
            logic is_4dw_tlp;

            if (pcie_addr[63 : 32] == 0) begin
                is_4dw_tlp = '0;
            end else begin
                is_4dw_tlp = '1;
            end

            pcie_hdr = '0;
            pcie_hdr[9 : 0]   = pcie_len[9 : 0];
            pcie_hdr[31 : 24] = 8'b01000000;
            pcie_hdr[29]      = is_4dw_tlp;
            pcie_hdr[35 : 32] = fbe;
            pcie_hdr[39 : 36] = lbe;
            if (is_4dw_tlp == 1) begin
                pcie_hdr[95 : 64]  = pcie_addr[63 : 32];
                pcie_hdr[127 : 98] = pcie_addr[31 : 2];
            end else begin
                pcie_hdr[95 : 66] = pcie_addr[31 : 2];
            end

            ret.data.data = data;

            ret.meta.data = '0;
            ret.meta.data[127 : 0]   = pcie_hdr;
            ret.meta.data[162 : 160] = 3'b010; // BAR ID
        end

        return ret;
    endfunction

    task send_data();
        pcie_info pcie_transactions[$];
        int unsigned packet_byte_cntr;
        int unsigned pcie_len;
        logic [MFB_ITEM_WIDTH-1 : 0]  data[];

        logic [MFB_ITEM_WIDTH/8-1:0]  fbe;
        logic [MFB_ITEM_WIDTH/8-1:0]  lbe = '0;
        logic [MFB_ITEM_WIDTH/8-1:0]  send_lbe = '0; // if pcie transaction have one dword then lbe is set to zero

        const int unsigned packet_len = (req.m_packet.size()+(MFB_ITEM_WIDTH/8-1))/(MFB_ITEM_WIDTH/8); //len in Dwords (rounded up, meaning the last DW has not to be full)

        int unsigned pcie_trans_cnt;
        int unsigned pcie_trans_ptr;
        string       debug_msg;

        debug_msg = "\n";

        debug_msg = {debug_msg,           "----------------------------------------------------------------\n"};
        debug_msg = {debug_msg, $sformatf("DRIVER: Transaction of length %0d B (%0d DW) on channel %0d\n", req.m_packet.size(), packet_len, m_channel)};
        debug_msg = {debug_msg,           "----------------------------------------------------------------\n"};

        packet_byte_cntr = 0;
        pcie_trans_cnt = 0;
        pcie_trans_ptr = m_driv_data.data_addr;
        pcie_transactions.delete();

        //////////////////////////////////
        // DATA SEND
        //
        // Iterates over the packet data and creates PCIE transactions from them
        while (packet_byte_cntr < req.m_packet.size()) begin

            int unsigned data_index;
            logic [64-1 : 0] pcie_addr;
            int unsigned rand_ret;

            //GENERATE RANDOM SIZE OF BLOCKS
            rand_ret = std::randomize(pcie_len) with {pcie_len dist {[1:63] :/ 75, [64:PCIE_LEN_MAX/2-1] :/ 15,  [PCIE_LEN_MAX/2:PCIE_LEN_MAX-1] :/ 8, PCIE_LEN_MAX :/ 2}; };
            if (rand_ret == 0) begin
                pcie_len = PCIE_LEN_MAX;
            end

            debug_msg = {debug_msg, "\n"};
            debug_msg = {debug_msg, $sformatf("\tPointer for transaction: 0x%h\n", pcie_trans_ptr)};
            debug_msg = {debug_msg, $sformatf("\tPointer mask: 0x%h\n", m_driv_data.data_mask)};
            debug_msg = {debug_msg, $sformatf("\tPCIE Transaction length: %0d DW\n", pcie_len)};
            debug_msg = {debug_msg, $sformatf("\tLast LBE: %b\n", lbe)};

            fbe = lbe_to_fbe(lbe);
            debug_msg = {debug_msg, $sformatf("\tDerived next FBE: %b\n", fbe)};

            if (packet_len <= (packet_byte_cntr/(MFB_ITEM_WIDTH/8) + pcie_len)) begin
                pcie_len = packet_len - packet_byte_cntr/(MFB_ITEM_WIDTH/8);
                lbe      = decode_lbe(req.m_packet.size() % (MFB_ITEM_WIDTH/8));
            end else begin
                assert(std::randomize(lbe) with {
                        if (pcie_len == 1){
                            $countones(lbe & fbe) > 0;
                            lbe inside {4'b1111, 4'b0111, 4'b0011, 4'b0001};
                        } else {
                            //lbe inside {4'b1111, 4'b0111, 4'b0011, 4'b0001};
                            lbe inside {4'b1000, 4'b1100, 4'b1010, 4'b1110, 4'b1001, 4'b1101, 4'b1011, 4'b1111, 4'b0100, 4'b0110, 4'b0101, 4'b0111, 4'b0010, 4'b0011, 4'b0001};
                        }
                    }) else `uvm_fatal(this.get_full_name(), "\n\tCannot randomize lbe");
            end

            debug_msg = {debug_msg, $sformatf("\tRemaining transaction length: %0d\n", pcie_len)};
            debug_msg = {debug_msg, $sformatf("\tCalculated LBE: %b\n", lbe)};

            // COPY DATA TO TEMPORARY VARIABLE
            data = new[pcie_len];
            data_index = 0;
            void'(std::randomize(data[0]));

            if (pcie_len > 1) begin
                void'(std::randomize(data[pcie_len-1]));

                //pealing FBE
                for (int unsigned jt = this.encode_fbe(fbe); jt < MFB_ITEM_WIDTH/8; jt++) begin
                    data[0][(jt+1)*8-1 -: 8] = req.m_packet[packet_byte_cntr + data_index];
                    data_index++;
                end

                //Except first and last PCI WORD
                for (int unsigned it = 1; it < pcie_len-1; it++) begin
                    data[it] = { << 8 {req.m_packet[packet_byte_cntr + data_index +: MFB_ITEM_WIDTH/8]}};
                    data_index += MFB_ITEM_WIDTH/8;
                end

                //pealing LBE
                for (int unsigned jt = 0; jt < this.encode_lbe(lbe); jt++) begin
                    data[pcie_len-1][(jt+1)*8-1 -: 8] = req.m_packet[packet_byte_cntr + data_index];
                    data_index++;
                end

                send_lbe = lbe;
            end else begin
                for (int unsigned jt = this.encode_fbe(fbe); jt < this.encode_lbe(lbe); jt++) begin
                    data[0][(jt+1)*8-1 -: 8] = req.m_packet[packet_byte_cntr + data_index];
                    data_index++;
                end

                fbe &= lbe;
                send_lbe = 0;
            end

            debug_msg = {debug_msg, $sformatf("\tOld byte cntr: %0d\n", packet_byte_cntr)};
            packet_byte_cntr += data_index;
            debug_msg = {debug_msg, $sformatf("\tData index: %0d\n", data_index)};
            debug_msg = {debug_msg, $sformatf("\tNew byte cntr: %0d\n", packet_byte_cntr)};

            pcie_addr = '0;
            pcie_addr[DATA_POINTER_WIDTH-1 : 0] = pcie_trans_ptr; // Address is in bytes
            pcie_addr[(DATA_POINTER_WIDTH+1+$clog2(CHANNELS))-1 : DATA_POINTER_WIDTH+1] = m_channel;
            pcie_addr[(DATA_POINTER_WIDTH+$clog2(CHANNELS)+1)] = 1'b0;
            pcie_transactions.push_back(create_pcie_req(pcie_addr, pcie_len, fbe, send_lbe, data, data_index));

            debug_msg = {debug_msg, "\n"};
            debug_msg = {debug_msg, "-----------------------------------------------\n"};
            debug_msg = {debug_msg, $sformatf("DRIVER: PCIe DATA TRANSACTION %0d on channel %0d\n", pcie_trans_cnt, m_channel)};
            debug_msg = {debug_msg, "-----------------------------------------------\n"};
            debug_msg = {debug_msg, $sformatf("\tdata_addr 0x%h(%0d)\n", pcie_trans_ptr, pcie_trans_ptr)};
            debug_msg = {debug_msg, $sformatf("\tpcie_addr 0x%h(%0d)\n", pcie_addr, pcie_addr)};
            debug_msg = {debug_msg, $sformatf("\tpcie_addr 0x%h(%0d) - CUTOUT\n", pcie_addr[DATA_POINTER_WIDTH-1 : 2], pcie_addr[DATA_POINTER_WIDTH-1 : 2])};
            debug_msg = {debug_msg, $sformatf("\tpcie_len  %0d dwords (%0d B)\n", pcie_len, data_index)};
            debug_msg = {debug_msg, $sformatf("\tfbe %b lbe %b\n", fbe, lbe)};
            debug_msg = {debug_msg, print_data(data)};

            debug_msg = {debug_msg, "\n"};

            pcie_trans_ptr = (pcie_trans_ptr + data_index) & m_driv_data.data_mask;
            pcie_trans_cnt++;
        end

        // Figure out if the channel is active to determine if the update of pointer and check of free
        // space needs to be issued.
        status_read(m_driv_data.chan_active_reg);
        debug_msg = {debug_msg, $sformatf("\tChan active: 0x%h \n", m_driv_data.chan_active_reg)};

        //(SHUFLE AND )SEND DATA
        // pcie_transactions.shuffle();

        for (int unsigned it = 0; it < pcie_transactions.size(); it++) begin
            int trans_byte_size = pcie_transactions[it].byte_size;
            debug_msg = {debug_msg, $sformatf("\tPutting transaction of size: %0d (free space: %0d)\n", trans_byte_size, m_driv_data.data_free_space)};

            if (m_driv_data.data_free_space < trans_byte_size) begin
                wait_for_free_space(trans_byte_size, 0);
                debug_msg = {debug_msg, $sformatf("\tNew free space after read: %0d\n", m_driv_data.data_free_space)};
            end

            m_data_export.put(m_channel, pcie_transactions[it].meta, pcie_transactions[it].data);

            m_driv_data.data_addr = (m_driv_data.data_addr + trans_byte_size) & m_driv_data.data_mask;
            debug_msg = {debug_msg, $sformatf("\tNew internal data ptr: 0x%h\n", m_driv_data.data_addr)};
            m_driv_data.data_free_space -= trans_byte_size;
        end

        debug_msg = {debug_msg, "\n"};

        //Allign pointer to PACKET ALLIGMENT
        if ((m_driv_data.data_addr % PACKET_ALIGNMENT) != 0) begin
            int unsigned size_to_allign;

            debug_msg = {debug_msg, $sformatf("\tRealigning ptr: 0x%h (free_space: %0d)\n", m_driv_data.data_addr, m_driv_data.data_free_space)};
            debug_msg = {debug_msg, $sformatf("\tPtr mask: %h\n", m_driv_data.data_mask)};
            size_to_allign = (PACKET_ALIGNMENT-(m_driv_data.data_addr % PACKET_ALIGNMENT));
            debug_msg = {debug_msg, $sformatf("\tRemaining size to align: %0d (0x%h)\n", size_to_allign, size_to_allign)};

            if (m_driv_data.data_free_space < size_to_allign)
                wait_for_free_space(size_to_allign, 0);

            m_driv_data.data_addr = (m_driv_data.data_addr + size_to_allign) & m_driv_data.data_mask;
            m_driv_data.data_free_space -= size_to_allign;
            debug_msg = {debug_msg, $sformatf("\tPtr after alignment: 0x%h (free_space: %0d)\n", m_driv_data.data_addr, m_driv_data.data_free_space)};
        end

        `uvm_info(this.get_full_name(), debug_msg, UVM_HIGH);

        if (m_driv_data.chan_active_reg != 0)
            ptr_write(m_regmodel_channel.sw_data_pointer_reg, m_driv_data.data_addr);

        // --------------------------------------------------------------
        // Parameter checks
        // --------------------------------------------------------------
        if (m_driv_data.data_free_space > m_driv_data.data_mask)
            `uvm_fatal(this.get_full_name(), $sformatf("\n\tDATA: The free space counter has an invalid value: %0d", m_driv_data.data_free_space));
    endtask

    // parameter allow_ptr_update is handed from the send_data function called
    // previously and it allows to send a DMA header when the channel gets a stop
    // request during packet reception
    task send_header(logic [16-1:0] packet_ptr);
        pcie_info pcie_transaction;
        int unsigned              pcie_len;
        logic [4-1:0]             fbe;
        logic [4-1:0]             lbe;
        logic [DMA_HDR_SIZE-1:0]  dma_hdr;
        logic [64-1 : 0]          pcie_addr;
        string debug_msg;

        //////////////////////////////////
        // DMA HEADER
        fbe                   = '1;
        lbe                   = '1;
        pcie_len              = 2;

        // DMA HDR Filling
        dma_hdr[15 : 0]  = req.m_packet.size();
        dma_hdr[31 : 16] = packet_ptr;
        dma_hdr[39 : 32] = '0;
        dma_hdr[63 : 40] = req.m_meta;

        pcie_addr = '0;
        pcie_addr[DATA_POINTER_WIDTH-1 : 0] = m_driv_data.hdr_addr*2*(MFB_ITEM_WIDTH/8); //Address is in DMA headers (64B)
        pcie_addr[(DATA_POINTER_WIDTH+1+$clog2(CHANNELS))-1 : DATA_POINTER_WIDTH+1] = m_channel;
        pcie_addr[(DATA_POINTER_WIDTH+$clog2(CHANNELS)+1)] = 1'b1;
        pcie_transaction = create_pcie_req(pcie_addr, pcie_len, fbe, lbe, {dma_hdr[31 : 0], dma_hdr[63 : 32]}, 8);

        debug_msg = "\n";
        debug_msg = {debug_msg, "-----------------------------------------------\n"};
        debug_msg = {debug_msg, $sformatf("DRIVER: PCIe HEADER TRANSACTION on channel %0d\n", m_channel)};
        debug_msg = {debug_msg, "-----------------------------------------------\n"};
        debug_msg = {debug_msg, $sformatf("\theader_addr 0x%h(%0d)\n", pcie_addr[DATA_POINTER_WIDTH-1 : 0], pcie_addr[DATA_POINTER_WIDTH-1 : 0])};
        debug_msg = {debug_msg, $sformatf("\theader_num  0x%h(%0d)\n", m_driv_data.hdr_addr, m_driv_data.hdr_addr)};
        debug_msg = {debug_msg, $sformatf("\tpcie_len  %0d dwords\n", pcie_len)};
        debug_msg = {debug_msg, $sformatf("\tfbe %b fbe %b\n", fbe, lbe)};
        debug_msg = {debug_msg, $sformatf("\tpacket size    %0dB\n", req.m_packet.size())};
        debug_msg = {debug_msg, $sformatf("\tpacket pointer 0x%h (%0d)\n", packet_ptr, packet_ptr)};
        debug_msg = {debug_msg, $sformatf("\tmeta %h\n", req.m_meta)};
        `uvm_info(this.get_full_name(), debug_msg, UVM_HIGH);

        //SEND DATA
        // ptr_read(m_regmodel_channel.control_reg, chan_active);
        if (m_driv_data.hdr_free_space == 0)
            wait_for_free_space(1, 1);

        m_data_export.put(m_channel, pcie_transaction.meta, pcie_transaction.data);

        //move hdr pointer
        m_driv_data.hdr_addr += 1;
        m_driv_data.hdr_addr &= m_driv_data.hdr_mask;
        m_driv_data.hdr_free_space -= 1;

        //actualize sdp_pointer
        if (m_driv_data.chan_active_reg != 0)
            ptr_write(m_regmodel_channel.sw_hdr_pointer_reg, m_driv_data.hdr_addr);

        // --------------------------------------------------------------
        // Parameter checks
        // --------------------------------------------------------------
        if (m_driv_data.hdr_free_space > m_driv_data.hdr_mask)
            `uvm_fatal(this.get_full_name(), $sformatf("\n\t HDR: The free space counter has an invalid value: %0d", m_driv_data.hdr_free_space));
    endtask

    task run_phase(uvm_phase phase);

        // Initial wait for the reset to drop
        wait(m_reset_terminate.is_reset() == 1);
        while(m_reset_terminate.has_been_reset() == 1)
            #(10ns);

        // Read masks of pointers in the beginning.
        ptr_read(m_regmodel_channel.data_mask_reg, m_driv_data.data_mask);
        ptr_read(m_regmodel_channel.hdr_mask_reg , m_driv_data.hdr_mask);

        m_driv_data.data_free_space = m_driv_data.data_mask;
        m_driv_data.hdr_free_space  = m_driv_data.hdr_mask;

        forever begin
            logic [16-1:0] packet_ptr;
            string debug_msg;

            seq_item_port.get_next_item(req);

            debug_msg = "\n";
            debug_msg = {debug_msg, "==========================================================\n"};
            debug_msg = {debug_msg, $sformatf("DRIVER: Got sequence item to channel %0d\n", m_channel)};
            debug_msg = {debug_msg, "==========================================================\n"};
            debug_msg = {debug_msg, req.convert2string()};

            debug_msg = {debug_msg, $sformatf("\n\n\tRead data pointer mask:   0x%h\n", m_driv_data.data_mask)};
            debug_msg = {debug_msg, $sformatf("\tRead header pointer mask: 0x%h\n", m_driv_data.hdr_mask)};
            `uvm_info(this.get_full_name(), debug_msg, UVM_HIGH);

            //align start of packet to PACKET_ALIGMENT
            packet_ptr = m_driv_data.data_addr;

            send_data();

            send_header(packet_ptr);

            seq_item_port.item_done();
        end
    endtask
endclass
