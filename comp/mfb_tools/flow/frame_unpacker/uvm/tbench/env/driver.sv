// driver.sv
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class driver#(HEADER_SIZE, VERBOSITY, PKT_MTU, MIN_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MVB_ITEM_WIDTH, OFF_PIPE_STAGES, ZERO_TS = 0, CHSUM_EN = 0, META_WIDTH = 0) extends uvm_component;
    `uvm_component_param_utils(uvm_superunpacketer::driver#(HEADER_SIZE, VERBOSITY, PKT_MTU, MIN_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MVB_ITEM_WIDTH, OFF_PIPE_STAGES, ZERO_TS, CHSUM_EN, META_WIDTH))

    localparam L2_HDR_WIDTH = 7;
    localparam L3_HDR_WIDTH = 9;

    uvm_seq_item_pull_port #(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH), uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH))                           seq_item_port_byte_array;
    uvm_seq_item_pull_port #(uvm_superpacket_header::sequence_item #(MVB_ITEM_WIDTH, HEADER_SIZE), uvm_superpacket_header::sequence_item #(MVB_ITEM_WIDTH, HEADER_SIZE)) seq_item_port_header;
    uvm_seq_item_pull_port #(uvm_superpacket_size::sequence_item, uvm_superpacket_size::sequence_item)                                                                   seq_item_port_sp_size;

    uvm_seq_item_pull_port #(uvm_logic_vector::sequence_item #(META_WIDTH), uvm_logic_vector::sequence_item #(META_WIDTH)) seq_item_port_chsum_hdr;

    mailbox#(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)) byte_array_export;
    mailbox#(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH))       logic_vector_export;

    // STATES
    parameter FIRST = 0;
    parameter DATA  = 1;

    uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)              byte_array_req;
    uvm_superpacket_header::sequence_item #(MVB_ITEM_WIDTH, HEADER_SIZE) info_req;
    uvm_superpacket_size::sequence_item                                  size_of_sp; // Size of superpacket in bytes with headers
    uvm_logic_vector::sequence_item #(META_WIDTH)                        chsum_hdr;
    uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)              byte_array_new;
    uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)              byte_array_out;
    uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH)                    logic_vector_out;

    int pkt_cnt_stat[OFF_PIPE_STAGES+1] = '{default:'0};
    int state                           = 0;
    int act_size                        = 0;
    int sp_cnt                          = 0;
    int hdr_cnt                         = 0;
    int pkt_cnt                         = 0;
    int end_of_packet                   = 0;
    int sup_align                       = 0;
    logic chsum_overflow                = 0;

    logic                              done = 1'b0;
    logic [HEADER_SIZE-1 : 0]          header;
    local logic [MFB_ITEM_WIDTH-1 : 0] data_fifo[$];

    string debug_msg;

    typedef struct{
        logic next;
        logic[HEADER_SIZE-1 : 0] hdr;
    } sp_info;



    function sp_info fill_header(uvm_superpacket_header::sequence_item #(MVB_ITEM_WIDTH, HEADER_SIZE) info, logic first);
        logic[HEADER_SIZE-1 : 0] hdr = '0;
        sp_info ret;
        int unsigned chsum_hdrs_len = 0;
        info.next = 1'b1;

        if((size_of_sp.sp_size - ((act_size + HEADER_SIZE/MFB_ITEM_WIDTH) + info.length)) < MIN_SIZE) begin
            info.next = 1'b0;
        end

        if ((act_size + HEADER_SIZE/MFB_ITEM_WIDTH + info.length) >= size_of_sp.sp_size) begin
            info.length = (size_of_sp.sp_size - (act_size + HEADER_SIZE/MFB_ITEM_WIDTH));
            info.next = 1'b0;
        end
        if (pkt_cnt == OFF_PIPE_STAGES) begin
            info.next = 1'b0;
        end
        end_of_packet = info.length + HEADER_SIZE/MFB_ITEM_WIDTH;

        if (ZERO_TS == 1) begin
            info.meta = '0;
        end
        if (CHSUM_EN) begin
            info.meta                                                            = '0;
            info.meta[L2_HDR_WIDTH-1                : 0                        ] = chsum_hdr.data[$clog2(PKT_MTU)+L2_HDR_WIDTH               -1 : $clog2(PKT_MTU)                          ];
            info.meta[L3_HDR_WIDTH+L2_HDR_WIDTH-1   : L2_HDR_WIDTH             ] = chsum_hdr.data[$clog2(PKT_MTU)+L2_HDR_WIDTH+L3_HDR_WIDTH  -1 : $clog2(PKT_MTU)+L2_HDR_WIDTH             ];
            info.meta[L3_HDR_WIDTH+L2_HDR_WIDTH+3-1 : L3_HDR_WIDTH+L2_HDR_WIDTH] = chsum_hdr.data[$clog2(PKT_MTU)+L2_HDR_WIDTH+L3_HDR_WIDTH+3-1 : $clog2(PKT_MTU)+L2_HDR_WIDTH+L3_HDR_WIDTH];
            chsum_hdrs_len = info.meta[L2_HDR_WIDTH-1 : 0] + info.meta[L3_HDR_WIDTH+L2_HDR_WIDTH-1: L2_HDR_WIDTH] + info.meta[L3_HDR_WIDTH+L2_HDR_WIDTH+3-1 : L3_HDR_WIDTH+L2_HDR_WIDTH] + 20;
            if ((act_size + HEADER_SIZE/MFB_ITEM_WIDTH + chsum_hdrs_len) >= size_of_sp.sp_size) begin
                chsum_overflow = 1;
            end
        end
        hdr = {info.meta, info.length};
        ret.hdr = hdr;
        ret.next = info.next;
        return ret;
    endfunction

    function void fill_tr(uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) pkt, sp_info sp_st);
        int align  = 0;
        string msg = "";
        logic [MFB_ITEM_WIDTH-1 : 0] tmp_data_fifo[$];
        uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH) tmp_data;
        tmp_data = uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)::type_id::create("tmp_data");

        align = MFB_BLOCK_SIZE - end_of_packet[3-1 : 0];
        if (sp_st.next == 1'b1 && end_of_packet[3-1 : 0] > 0) begin
            end_of_packet += align;
        end

        for (int i = 0; i < end_of_packet; i++) begin
            if (i < HEADER_SIZE/MFB_ITEM_WIDTH) begin
                data_fifo.push_back(sp_st.hdr[(i+1)*MFB_ITEM_WIDTH-1 -: MFB_ITEM_WIDTH]);
            end else if (i < pkt.data.size() + (HEADER_SIZE/MFB_ITEM_WIDTH)) begin
                data_fifo.push_back(pkt.data[i - (HEADER_SIZE/MFB_ITEM_WIDTH)]);
                tmp_data_fifo.push_back(pkt.data[i - (HEADER_SIZE/MFB_ITEM_WIDTH)]);
            end else begin
                data_fifo.push_back('0);
            end

            act_size++;
        end
        tmp_data.data = tmp_data_fifo;
        debug_msg = {debug_msg, $sformatf("PACKET %s\n",  tmp_data.convert2string())};

        if (sp_st.next == 1'b0 && end_of_packet[3-1 : 0]) begin
            for (int i = 0; i < align; i++) begin
                data_fifo.push_back('0);
            end
        end

        if (act_size == size_of_sp.sp_size && VERBOSITY >= 3) begin
            msg = {msg, $sformatf("\tSIZE OF FIFO %d\n",  data_fifo.size())};
            msg = {msg, $sformatf("\tSIZE OF SP %d\n",  size_of_sp.sp_size)};
            `uvm_info(this.get_full_name(), msg ,UVM_FULL)
        end
    endfunction

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);

        seq_item_port_byte_array = new("seq_item_port_byte_array", this);
        seq_item_port_header     = new("seq_item_port_header", this);
        seq_item_port_sp_size    = new("seq_item_port_sp_size", this);
        seq_item_port_chsum_hdr  = new("seq_item_port_chsum_hdr", this);

        byte_array_export        = new();
        logic_vector_export      = new();
    endfunction

    // ------------------------------------------------------------------------
    // Starts driving signals to interface
    task run_phase(uvm_phase phase);
        localparam MIN_DATA_SIZE = MIN_SIZE - HEADER_SIZE/MFB_ITEM_WIDTH;
        logic[16-1 : 0] len_with_hdr = 0;
        string msg = "";
        sp_info sp_st;
        int unsigned wait_period;

        forever begin

            wait_period = $urandom_range(0, 500);

            #(wait_period*1ns);
            done = 1'b0;
            chsum_overflow = 0;
            debug_msg = "\n";
            debug_msg = {debug_msg, $sformatf("\n ================ SUPERPACKET %d IN DRIVER =============== \n",  sp_cnt+1)};
            while (done != 1'b1) begin
                seq_item_port_byte_array.get_next_item(byte_array_req);
                pkt_cnt++;
                seq_item_port_header.get_next_item(info_req);
                if (CHSUM_EN) begin
                    seq_item_port_chsum_hdr.get_next_item(chsum_hdr);
                end

                assert($cast(byte_array_new, byte_array_req.clone()));
                info_req.length = byte_array_new.data.size();
                sp_st.hdr = '0;

                if (state == FIRST) begin
                    state          = DATA;

                    byte_array_out = uvm_logic_vector_array::sequence_item #(MFB_ITEM_WIDTH)::type_id::create("byte_array_out");
                    logic_vector_out = uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH)::type_id::create("logic_vector_out");

                    logic_vector_out.data = info_req.meta;
                    logic_vector_export.put(logic_vector_out);
                    hdr_cnt++;

                    seq_item_port_sp_size.get_next_item(size_of_sp);
                end

                sp_st = fill_header(info_req, 1'b1);
                debug_msg = {debug_msg, $sformatf("CHSUM HDR: \n")};
                debug_msg = {debug_msg, $sformatf("PAYLOAD LEN %d\n",  sp_st.hdr[16      -1 : 0     ])};
                debug_msg = {debug_msg, $sformatf("L2 LEN %d\n",  sp_st.hdr[16+7    -1 : 16    ])};
                debug_msg = {debug_msg, $sformatf("L3 LEN %d\n",  sp_st.hdr[16+7+9  -1 : 16+7  ])};
                debug_msg = {debug_msg, $sformatf("FLAG   %b\n",  sp_st.hdr[16+7+9+3-1 : 16+7+9])};

                len_with_hdr = byte_array_new.size() + HEADER_SIZE/MFB_ITEM_WIDTH;
                if (VERBOSITY >= 3) begin
                    msg = {msg, $sformatf("\n ================ DEBUG IN DRIVER =============== \n")};
                    msg = {msg, $sformatf("\tlen with hdr %d\n",  len_with_hdr)};
                    msg = {msg, $sformatf("\tact_size %d\n",  act_size)};
                    msg = {msg, $sformatf("\tMIN DATA SIZE %d\n",  MIN_DATA_SIZE)};
                    msg = {msg, $sformatf("\tHEADER_SIZE/MFB_ITEM_WIDTH %d\n",  HEADER_SIZE/MFB_ITEM_WIDTH)};
                    msg = {msg, $sformatf("\tsize_of_sp.sp_size %d\n",  size_of_sp.sp_size)};
                    msg = {msg, $sformatf("\tALIGN %d\n",  MFB_BLOCK_SIZE-len_with_hdr[3-1 : 0])};
                    msg = {msg, $sformatf("\tSOLUTION %d\n",  signed'((size_of_sp.sp_size - (act_size + len_with_hdr + HEADER_SIZE/MFB_ITEM_WIDTH + MIN_DATA_SIZE + (MFB_BLOCK_SIZE - int'(len_with_hdr[3-1 : 0]) )))))};
                    `uvm_info(this.get_full_name(), msg ,UVM_FULL)
                end

                // Check if there is a place for another packet
                if (signed'((size_of_sp.sp_size - (act_size + len_with_hdr + HEADER_SIZE/MFB_ITEM_WIDTH + MIN_DATA_SIZE + (MFB_BLOCK_SIZE - int'(len_with_hdr[3-1 : 0]) )))) < 0) begin
                    sp_st.next = 1'b0;
                end

                if (!chsum_overflow) begin
                    fill_tr(byte_array_new, sp_st);
                end

                if (sp_st.hdr[16-1 : 0] < MIN_DATA_SIZE) begin
                    `uvm_fatal(this.get_full_name(), "Data length is too small.");
                end

                if (sp_st.next == 1'b0) begin
                    done                = 1'b1;
                    pkt_cnt_stat[pkt_cnt] += 1;
                    pkt_cnt             = 1'b0;
                    byte_array_out.data = data_fifo;
                    sup_align = MFB_BLOCK_SIZE - (size_of_sp.sp_size % MFB_BLOCK_SIZE);
                    if (byte_array_out.size() > size_of_sp.sp_size + sup_align) begin
                        `uvm_fatal(this.get_full_name(), "Data length is too long.");
                    end
                    // debug_msg = {debug_msg, $sformatf("SUPERPACKET %s\n",  byte_array_out.convert2string())};
                    // $write("SP LEN %d\n", byte_array_out.size());
                    byte_array_export.put(byte_array_out);
                    sp_cnt++;
                    act_size = 0;
                    data_fifo.delete();
                    byte_array_out = null;
                    state = FIRST;
                    seq_item_port_sp_size.item_done();
                    debug_msg = {debug_msg, $sformatf("\n ====================================== \n")};
                    `uvm_info(this.get_full_name(), debug_msg ,UVM_FULL)
                end
                end_of_packet = 0;
                seq_item_port_byte_array.item_done();
                seq_item_port_header.item_done();
                if (CHSUM_EN) begin
                    seq_item_port_chsum_hdr.item_done();
                end

            end
        end
    endtask

    function void report_phase(uvm_phase phase);
        string msg = "";

        msg = {msg, $sformatf("\n\tNumber of packets in SP statistic:\n")};
        for (int unsigned it = 0; it < OFF_PIPE_STAGES; it++) begin
            msg = {msg, $sformatf("\tCounter number %d: %d\n",  it, pkt_cnt_stat[it])};
        end
        `uvm_info(this.get_full_name(), msg ,UVM_FULL)
    endfunction


endclass
