// model.sv: Model of implementation
// Copyright (C) 2022-2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class discard #(int unsigned CHANNELS) extends uvm_component;
    `uvm_component_param_utils(uvm_tx_dma_calypte::discard #(CHANNELS))

    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(1)) m_internal_meta_analysis_fifo;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        m_internal_meta_analysis_fifo = new("m_internal_meta_analysis_fifo", this);
    endfunction

    task get_tr(output logic drop);
        uvm_logic_vector::sequence_item#(1) drop_tr;
        m_internal_meta_analysis_fifo.get(drop_tr);
        drop = drop_tr.data;
    endtask
endclass

class model #(
    int unsigned USR_MFB_ITEM_WIDTH,
    int unsigned PCIE_CQ_MFB_ITEM_WIDTH,
    int unsigned CHANNELS,
    int unsigned DATA_POINTER_WIDTH,
    int unsigned USR_MFB_META_WIDTH,
    string DEVICE
) extends uvm_component;

    `uvm_component_param_utils(uvm_tx_dma_calypte::model #(USR_MFB_ITEM_WIDTH, PCIE_CQ_MFB_ITEM_WIDTH, CHANNELS, DATA_POINTER_WIDTH, USR_MFB_META_WIDTH, DEVICE))

    localparam DATA_ADDR_MASK = 2**DATA_POINTER_WIDTH-1;

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(PCIE_CQ_MFB_ITEM_WIDTH))                m_cq_data_analysis_fifo;
    uvm_tlm_analysis_fifo #(uvm_logic_vector      ::sequence_item #(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)) m_cq_meta_analysis_fifo;
    uvm_analysis_port     #(uvm_logic_vector_array::sequence_item #(USR_MFB_ITEM_WIDTH))                    m_usr_data_analysis_port;
    uvm_analysis_port     #(uvm_logic_vector      ::sequence_item #(USR_MFB_META_WIDTH))                    m_usr_meta_analysis_port;

    local uvm_tx_dma_calypte_regs::regmodel_top #(CHANNELS) m_regmodel_top;

    protected int unsigned m_discard_wait;
    discard #(CHANNELS) m_discard_comp;

    // Counters for all of the channels
    protected int unsigned m_pcie_transactions;
    protected int unsigned m_dma_transactions;
    protected int unsigned m_drop_transactions;

    // Channel specific statisics
    typedef struct{
        int unsigned pcie_transactions;
        int unsigned dma_transactions;
        int unsigned drop_transactions;

        int unsigned dma_transactions_bytes;
        int unsigned drop_transactions_bytes;

        time  infs[string];

        logic [8-1:0] memory [2**DATA_POINTER_WIDTH];
    } channel_info_t;

    channel_info_t m_channel_info [CHANNELS];

    function new (string name, uvm_component parent = null);
        super.new(name, parent);

        m_cq_data_analysis_fifo  = new("m_cq_data_analysis_fifo",  this);
        m_cq_meta_analysis_fifo  = new("m_cq_meta_analysis_fifo",  this);
        m_usr_data_analysis_port = new("m_usr_data_analysis_port", this);
        m_usr_meta_analysis_port = new("m_usr_meta_analysis_port", this);

        m_pcie_transactions = 0;
        m_dma_transactions  = 0;
        m_drop_transactions = 0;

        for (int unsigned it = 0; it < CHANNELS; it++) begin
            m_channel_info[it].pcie_transactions       = 0;
            m_channel_info[it].dma_transactions        = 0;
            m_channel_info[it].drop_transactions       = 0;
            m_channel_info[it].dma_transactions_bytes  = 0;
            m_channel_info[it].drop_transactions_bytes = 0;
        end
    endfunction

    function void regmodel_set(uvm_tx_dma_calypte_regs::regmodel_top #(CHANNELS) regmodel);
        this.m_regmodel_top = regmodel;
    endfunction

    function void time_add (int unsigned channel, time inf_time[string], int unsigned id);
        foreach(inf_time[it]) begin
           m_channel_info[channel].infs[$sformatf("%s(%0d)", it, id)] = inf_time[it];
        end
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (m_cq_data_analysis_fifo.used() != 0);
        ret |= (m_cq_meta_analysis_fifo.used() != 0);
        ret |= m_discard_wait;
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        m_discard_comp = discard #(CHANNELS)::type_id::create("m_discard_comp", this);
    endfunction

    function int unsigned encode_fbe(logic [PCIE_CQ_MFB_ITEM_WIDTH/8-1 : 0] be);
        int unsigned it = 0;

        if (be != 0) begin
            while (it < PCIE_CQ_MFB_ITEM_WIDTH/8 && be[it] == 0) begin
                it++;
            end
        end
        return it;
    endfunction

    function int unsigned encode_lbe(logic [PCIE_CQ_MFB_ITEM_WIDTH/8-1 : 0] be);
        int unsigned it  = PCIE_CQ_MFB_ITEM_WIDTH/8;

        if (be != 0) begin
            while (it > 0 && be[it-1] == 0) begin
                it--;
            end;
        end
        return it;
    endfunction

    task run_phase(uvm_phase phase);
        uvm_logic_vector_array::sequence_item#(PCIE_CQ_MFB_ITEM_WIDTH)          cq_data_tr;
        uvm_logic_vector::sequence_item#(sv_pcie_meta_pack::PCIE_CQ_META_WIDTH) cq_meta_tr;
        uvm_logic_vector_array::sequence_item#(USR_MFB_ITEM_WIDTH)              usr_tx_data_tr;
        uvm_logic_vector::sequence_item#(USR_MFB_META_WIDTH)                    usr_tx_meta_tr;

        string                         debug_msg;
        logic                          drop;
        logic [DATA_POINTER_WIDTH-1:2] addr;
        int unsigned                   dword_cnt;
        logic [$clog2(CHANNELS)-1:0]   channel;
        logic [1-1:0]                  hdr_inf;
        logic                          res;
        int unsigned                   fbe_ext;
        int unsigned                   lbe_ext;
        int unsigned                   fbe;
        int unsigned                   lbe;
        // This index points to a DW where the user data in the PCIE transaction begin.
        // Each device has a different value of this index.
        int unsigned                   usr_data_begin_idx;

        forever begin
            logic [64-1:0] pcie_addr;

            //GET PCIE TRANSACTION
            m_cq_data_analysis_fifo.get(cq_data_tr);
            m_cq_meta_analysis_fifo.get(cq_meta_tr);

            m_discard_wait = 1;
            // Get information if the current transaction should be dropped
            m_discard_comp.get_tr(drop);
            m_discard_wait = 0;

            // Parsing the input data according to the selected device
            if (DEVICE == "ULTRASCALE") begin
                dword_cnt          = cq_data_tr.data[2][11-1 : 0];
                pcie_addr          = {cq_data_tr.data[1], cq_data_tr.data[0]};
                fbe_ext            = cq_meta_tr.data[167-1 : 163];
                lbe_ext            = dword_cnt > 1 ? cq_meta_tr.data[171-1 : 167] : cq_meta_tr.data[167-1 : 163];
                usr_data_begin_idx = 4;

            end else begin
                logic is_4dw_tlp;
                dword_cnt  = cq_meta_tr.data[10-1 : 0];
                is_4dw_tlp = cq_meta_tr.data[29];

                if (is_4dw_tlp == 1)
                    pcie_addr = {cq_meta_tr.data[95:64], cq_meta_tr.data[127:96]};
                else
                    pcie_addr = cq_meta_tr.data[95:64];

                fbe_ext            = cq_meta_tr.data[35:32];
                lbe_ext            = dword_cnt > 1 ? cq_meta_tr.data[39:36] : cq_meta_tr.data[35:32];
                usr_data_begin_idx = 0;
            end

            if (dword_cnt == 0) begin
                dword_cnt  = 1024;
            end

            addr       = pcie_addr[DATA_POINTER_WIDTH-1 : 2];
            channel    = pcie_addr[(DATA_POINTER_WIDTH+1+$clog2(CHANNELS))-1 : DATA_POINTER_WIDTH+1];
            hdr_inf    = pcie_addr[(DATA_POINTER_WIDTH+1+$clog2(CHANNELS))];

            m_pcie_transactions++;
            m_channel_info[channel].pcie_transactions++;

            debug_msg = "\n";
            debug_msg = { debug_msg, $sformatf("================================================================================= \n")};
            debug_msg = { debug_msg, $sformatf("MODEL INPUT PCIe TRANSACTION %0d\n", m_pcie_transactions)};
            debug_msg = { debug_msg, $sformatf("================================================================================= \n")};
            debug_msg = { debug_msg, $sformatf("CHANNEL     : %0d\n", channel)};
            debug_msg = { debug_msg, $sformatf("TRANSACTION : %0d\n", m_channel_info[channel].pcie_transactions)};
            debug_msg = { debug_msg, $sformatf("DROP        : %0d\n", drop)};
            debug_msg = { debug_msg, $sformatf("ADDR        : %0d\n", {addr, 2'b00})};
            debug_msg = { debug_msg, $sformatf("HDR FLAG    : %0b\n", (hdr_inf != 1'b0))};
            debug_msg = { debug_msg, $sformatf("DW CNT      : %0d\n", dword_cnt)};
            debug_msg = { debug_msg, $sformatf("FBE         : %b\n", fbe_ext)};
            debug_msg = { debug_msg, $sformatf("LBE         : %b\n", lbe_ext)};
            debug_msg = { debug_msg, $sformatf("DATA        : %s\n", cq_data_tr.convert2string())};
            debug_msg = { debug_msg, $sformatf("================================================================================= \n")};
            `uvm_info(this.get_full_name(), debug_msg, UVM_MEDIUM);

            //if PCIE transaction is not DMA HEADER
            if (hdr_inf == 1'b0) begin
                fbe = encode_fbe(fbe_ext);

                if (dword_cnt <= 1) begin
                    lbe = encode_lbe(lbe_ext);
                    for (int unsigned it = fbe; it < lbe; it++) begin
                         m_channel_info[channel].memory[{addr, 2'b00} + it] = cq_data_tr.data[usr_data_begin_idx][(it+1)*8-1 -: 8];
                    end
                end else begin
                    logic [DATA_POINTER_WIDTH-1:0] addr_act = {addr, 2'b00};
                    lbe = encode_lbe(lbe_ext);
                    //peeling start
                    for (int unsigned it = fbe; it < 4; it++) begin
                         m_channel_info[channel].memory[addr_act + it] = cq_data_tr.data[usr_data_begin_idx][(it+1)*8-1 -: 8];
                    end
                    addr_act = (addr_act + 4) & DATA_ADDR_MASK;
                    //Main loop
                    for (int unsigned it = 1; (it+1) < dword_cnt; it++) begin
                         {<<8{m_channel_info[channel].memory[addr_act +: 4]}} = cq_data_tr.data[usr_data_begin_idx + it];
                         addr_act = (addr_act + 4) & DATA_ADDR_MASK;
                    end
                    //peeling end
                    for (int unsigned it = 0; it < lbe; it++) begin
                         m_channel_info[channel].memory[addr_act + it] = cq_data_tr.data[usr_data_begin_idx + dword_cnt-1][(it+1)*8-1 -: 8];
                    end
                end

                this.time_add (channel, cq_data_tr.start, m_pcie_transactions);
                this.time_add (channel, cq_meta_tr.start, m_pcie_transactions);
            end else begin

                //if PCIE transaction is DMA HEADER then create output packečt and send it
                logic [16-1 : 0] packet_size;
                logic [24-1 : 0] dma_meta;
                logic [DATA_POINTER_WIDTH-1 : 0] frame_pointer;

                packet_size   = cq_data_tr.data[usr_data_begin_idx][16-1 : 0];
                frame_pointer = cq_data_tr.data[usr_data_begin_idx][32-1 : 16];
                dma_meta      = cq_data_tr.data[usr_data_begin_idx+1][32-1 : 8];

                if (drop == 1'b0) begin
                    usr_tx_data_tr      = uvm_logic_vector_array::sequence_item #(USR_MFB_ITEM_WIDTH)::type_id::create("usr_tx_data_tr", this);
                    usr_tx_meta_tr      = uvm_logic_vector::sequence_item #(USR_MFB_META_WIDTH)::type_id::create("usr_tx_meta_tr", this);

                    usr_tx_data_tr.start = m_channel_info[channel].infs;
                    usr_tx_data_tr.time_array_add(cq_data_tr.start);
                    usr_tx_data_tr.time_array_add(cq_meta_tr.start);
                    usr_tx_meta_tr.start = m_channel_info[channel].infs;
                    usr_tx_meta_tr.time_array_add(cq_data_tr.start);
                    usr_tx_meta_tr.time_array_add(cq_meta_tr.start);

                    usr_tx_data_tr.data = new[packet_size];
                    for (int unsigned it = 0; it < packet_size; it++) begin
                        int unsigned dma_mem_addr = (frame_pointer + it) & DATA_ADDR_MASK;
                        usr_tx_data_tr.data[it] = m_channel_info[channel].memory[dma_mem_addr];
                    end
                    usr_tx_meta_tr.data = {packet_size, channel, dma_meta};

                    m_dma_transactions++;
                    m_channel_info[channel].dma_transactions++;
                    m_channel_info[channel].dma_transactions_bytes += packet_size;

                    debug_msg = "\n";
                    debug_msg = {debug_msg, $sformatf("================================================================================= \n")};
                    debug_msg = {debug_msg, $sformatf("MODEL OUTPUT DMA TRANSACTION %0d\n", m_dma_transactions)};
                    debug_msg = {debug_msg, $sformatf("================================================================================= \n")};
                    debug_msg = {debug_msg, $sformatf("CHANNEL              : %0d\n", channel)};
                    debug_msg = {debug_msg, $sformatf("TRANSACTION          : %0d\n", m_channel_info[channel].dma_transactions)};
                    debug_msg = {debug_msg, $sformatf("FRAME POINTER        : %0d\n", frame_pointer)};
                    debug_msg = {debug_msg, $sformatf("SIZE IN BYTES        : %0d\n", packet_size)};
                    debug_msg = {debug_msg, $sformatf("================================================================================= \n")};
                    debug_msg = {debug_msg, $sformatf("OUT META: %s\n", usr_tx_meta_tr.convert2string())};
                    debug_msg = {debug_msg, $sformatf("OUT DATA: %s\n", usr_tx_data_tr.convert2string())};
                    debug_msg = {debug_msg, $sformatf("================================================================================= \n")};
                    `uvm_info(this.get_full_name(), debug_msg, UVM_MEDIUM)

                    m_usr_data_analysis_port.write(usr_tx_data_tr);
                    m_usr_meta_analysis_port.write(usr_tx_meta_tr);
                end else begin
                    m_drop_transactions++;
                    m_channel_info[channel].drop_transactions++;
                    m_channel_info[channel].drop_transactions_bytes += packet_size;

                    debug_msg = "\n";
                    debug_msg = {debug_msg, $sformatf("================================================================================= \n")};
                    debug_msg = {debug_msg, $sformatf("MODEL DROP %0d\n", m_drop_transactions)};
                    debug_msg = {debug_msg, $sformatf("================================================================================= \n")};
                    debug_msg = {debug_msg, $sformatf("CHANNEL              : %0d\n", channel)};
                    debug_msg = {debug_msg, $sformatf("TRANSACTION          : %0d\n", m_channel_info[channel].drop_transactions)};
                    debug_msg = {debug_msg, $sformatf("FRAME POINTER        : %0d\n", frame_pointer)};
                    debug_msg = {debug_msg, $sformatf("SIZE IN BYTES        : %0d\n", packet_size)};
                    debug_msg = {debug_msg, $sformatf("================================================================================= \n")};
                    debug_msg = {debug_msg, $sformatf("OUT META: %s\n", usr_tx_meta_tr.convert2string())};
                    debug_msg = {debug_msg, $sformatf("OUT DATA: %s\n", usr_tx_data_tr.convert2string())};
                    debug_msg = {debug_msg, $sformatf("================================================================================= \n")};
                    `uvm_info(this.get_full_name(), debug_msg, UVM_MEDIUM)
                end

                m_channel_info[channel].infs.delete();
            end
        end
    endtask
endclass
