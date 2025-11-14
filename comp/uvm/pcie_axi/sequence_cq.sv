
//-- sequence.sv: Convert PCIE transaction to axi Trasnactions
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet>
//-- SPDX-License-Identifier: BSD-3-Clause



class sequence_base_cq #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    logic STRADDLING
) extends uvm_common::sequence_base#(
    config_sequence,
    uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, tuser_width_get(ITEMS, AXI_CQ))
);
    `uvm_object_param_utils(uvm_pcie_axi::sequence_base_cq #(ITEMS, ITEM_WIDTH, STRADDLING));
    `uvm_declare_p_sequencer(uvm_axi::sequencer #(ITEMS, ITEM_WIDTH, tuser_width_get(ITEMS, AXI_CQ)));

    localparam PACKET_MAX = ITEMS < 16 || STRADDLING == 0 ? 1 : 2;
    localparam BE_INDEX   = ITEMS < 16 ? 8 : 16;
    localparam REGIONS_NUM = PACKET_MAX;
    localparam REGION_SIZE = ITEMS/PACKET_MAX;
    localparam SOF_INDEX  = ITEMS < 16 ? 40 : 80;
    localparam EOF_INDEX  = 86;
    localparam FBE_INDEX  = ITEMS < 16 ? 0 : 0;
    localparam LBE_INDEX  = ITEMS < 16 ? 4 : 8;


    int unsigned transactions_min = 10;
    int unsigned transactions_max = 300;
    rand int unsigned transactions;


    rand int unsigned rdy_probability_min;
    rand int unsigned rdy_probability_max;

    rand int unsigned next_pkt;

    constraint c_transactions {
        transactions inside {[transactions_min:transactions_max]};
    }

    // Probability of next packet be with smalles possible space
    constraint c_next_pkt {
        next_pkt inside {[0:100]};
    }

    constraint c_probability {
        rdy_probability_min <= rdy_probability_max;
        rdy_probability_min dist {
            cfg.rdy_probability_min  := 13,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*0/10:cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*1/10] :/18,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*0/10:cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*1/10] :/8,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*0/10:cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*1/10] :/7,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*0/10:cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*1/10] :/6,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*0/10:cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*1/10] :/5,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*0/10:cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*1/10] :/4,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*0/10:cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*1/10] :/5,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*0/10:cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*1/10] :/6,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*0/10:cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*1/10] :/7,
             // verilog_lint: waive line-length
            [cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*0/10:cfg.rdy_probability_min + (cfg.rdy_probability_max-cfg.rdy_probability_min)*1/10] :/8,
            cfg.rdy_probability_max := 13
        };
    }

    protected uvm_common::fifo#(uvm_pcie::header) in_fifo;

    typedef enum {PKT_NEW, PKT_HDR, PKT_FBE, PKT_DATA, PKT_NONE, PKT_SPACE} state_t;
    protected state_t        state;
    protected logic [32-1:0] data[$];
    protected logic [4-1:0]  fbe;
    protected logic [4-1:0]  lbe;

    protected int unsigned space;
    protected int unsigned send_data;

    function new(string name = "uvm_pcie_axi::sequence_simple_cq");
        super.new(name);
        space     = 0;
        send_data = 0;
    endfunction

    function void item_done();
        //in_fifo.item_done();
        data.delete();
    endfunction

    task try_get(output uvm_pcie::header hdr);

        if (transactions != 0 && !p_sequencer.reset_sync.is_reset()) begin
            in_fifo.try_get(hdr);
            if (hdr != null) begin
                transactions--;
            end
        end
    endtask

    // This taks create axi transaction
    virtual task create_sequence_item(ref uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, tuser_width_get(ITEMS, AXI_CQ)) gen);
        int unsigned region;
        int unsigned sof_num;
        int unsigned eof_num;
        gen.tuser = 0;
        gen.tkeep = '0;
        gen.tvalid = 0;
        gen.tlast = 0;

        if (STRADDLING == 0) begin
            gen.tuser[83:82] = 'x;
            gen.tuser[85:84] = 'x;
            gen.tuser[87:86] = 'x;
            gen.tuser[91:88] = 'x;
            gen.tuser[95:92] = 'x;
        end

        if (state == PKT_SPACE) begin
            if (space == 0) begin
                send_data = 0;
                state = PKT_NONE;
            end else begin
                space--;
                void'(gen.randomize());
                gen.tvalid = 0;
                return;
            end
        end

        region = 0;
        sof_num = 0;
        eof_num = 0;
        while (region < REGIONS_NUM && state != PKT_SPACE) begin
            int unsigned index = region*REGION_SIZE;


            if (state == PKT_NONE) begin
                uvm_pcie::request_header hdr;
                uvm_pcie::header tmp_hdr;

                try_get(tmp_hdr);
                if (tmp_hdr != null && $cast(hdr, tmp_hdr)) begin
                    logic[32-1:0] hdr_axi[4];
                    logic [8-1:0] target_fce = 0;

                    uvm_pcie_axi::hdr_cq_set(hdr_axi, hdr, target_fce, cfg.bar);
                    data = {hdr_axi, hdr.data};
                    send_data += data.size();
                    //fbe = hdr.fbe;
                    fbe = hdr.fbe; // TODO: NO FBE IN response
                    lbe = hdr.lbe;

                    state = PKT_HDR;
                end else begin
                    //Quit loop. There is no pakcet to send
                    state = PKT_NONE;
                    region = REGIONS_NUM;
                end
            end

            if (state == PKT_HDR) begin
                //Set SOP and SOP pointer
                gen.tuser[sof_num + SOF_INDEX] = 1'b1;
                if (ITEMS >= 16) begin //SOP pos is only in 512 bit width interface
                    gen.tuser[(sof_num+1)*2 + PACKET_MAX + SOF_INDEX-1 -: 2] = {region, 1'b0};
                end

                //COPY HEADER
                gen.tdata[(index+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.pop_front();
                gen.tuser[(index+1)*4 + BE_INDEX-1 -: 4] = 0;
                gen.tkeep[index] = 1;
                index++;

                gen.tdata[(index+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.pop_front();
                gen.tuser[(index+1)*4 + BE_INDEX-1 -: 4] = 0;
                gen.tkeep[index] = 1;
                index++;

                gen.tdata[(index+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.pop_front();
                gen.tuser[(index+1)*4 + BE_INDEX-1 -: 4] = 0;
                gen.tkeep[index] = 1;
                index++;

                gen.tdata[(index+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.pop_front();
                gen.tuser[(index+1)*4 + BE_INDEX-1 -: 4] = 0;
                gen.tkeep[index] = 1;
                index++;

                // Change lbe shouldnt rewrite
                // header be and data fbe. So we change it
                // acording to correct value
                if (data.size() == 0) begin
                    lbe = 0; // ONLY HEADER
                    state = PKT_DATA;
                end else if (data.size() == 1) begin
                    lbe = fbe; // only fbe is used
                    state = PKT_FBE;
                end else begin
                    lbe = lbe;
                    state = PKT_FBE;
                end
                // set FBE and LBE
                gen.tuser[(sof_num +1)*4 + FBE_INDEX-1 -: 4] = fbe;
                gen.tuser[(sof_num +1)*4 + LBE_INDEX-1 -: 4] = lbe;
                sof_num++;
            end

            //be carefull there can be header withnout any data
            if (state == PKT_FBE && data.size() > 0) begin
                gen.tdata[(index+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.pop_front();
                gen.tuser[(index+1)*4 + BE_INDEX-1 -: 4] = fbe;
                gen.tkeep[index] = 1;
                index++;
                state = PKT_DATA;
            end

            while (state == PKT_DATA && index < (region+1)*REGION_SIZE && data.size() > 0) begin
                gen.tdata[(index+1)*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.pop_front();
                gen.tuser[(index+1)*4 + BE_INDEX-1 -: 4] = 4'b1111;
                gen.tkeep[index] = 1;
                index++;
            end

            if (state == PKT_DATA && data.size() == 0) begin
                // Don't write lbe when data size is 0 -> Here is bug. Because
                // If there is only header then lbe shoudnt be writen (READ
                // HEADER)
                // Don't override fbe when data size is 1
                gen.tuser[(index)*4 + BE_INDEX-1 -: 4] = lbe;
                gen.tlast = 1;

                if (ITEMS >= 16) begin
                    //SET EOF and EOF position signal
                    gen.tuser[eof_num + EOF_INDEX] = 1'b1;
                    gen.tuser[(eof_num+1)*4 + PACKET_MAX + EOF_INDEX-1 -: 4] = index-1;
                end

                eof_num++;
                item_done();

                if ($urandom_range(0, 99) < next_pkt && STRADDLING == 1) begin
                    state = PKT_NONE;
                end else begin
                    int unsigned rdy_prob;

                    //count space size;
                    rdy_prob = $urandom_range(rdy_probability_min, rdy_probability_max);
                    // SPACE send whole empty words
                    space = send_data*(100-rdy_prob)/rdy_prob/ITEMS;

                    state = PKT_SPACE;
                    region = REGIONS_NUM;
                end
            end
            region++;
        end

        gen.tvalid = |gen.tkeep;
    endtask

    task send_empty_frame();
        start_item(req);
        req.randomize();
        req.tvalid = 0;
        finish_item(req);
    endtask

    task send_frame();
        // If reset then send empty frame
        if (p_sequencer.reset_sync.has_been_reset()) begin
            if (data.size() != 0) begin
                item_done();
            end

            req.randomize();
            req.tvalid = 0;
            state = PKT_NONE;
        end

        //SEND FRAME
        start_item(req);
        finish_item(req);
    endtask

    task body;
        uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, tuser_width_get(ITEMS, AXI_CQ)) gen;

        assert((STRADDLING == 0 && ITEMS <= 16) ||
               (STRADDLING == 1 && ITEMS == 16)
        ) else begin
            `uvm_fatal(m_sequencer.get_full_name(), $sformatf("\n\tSTRADDLING IS NOT IMPLEMENTED --\n\tSTRADDLING %0d\n\tITEMS %0d", STRADDLING, ITEMS));
        end

        if(!uvm_config_db#(uvm_common::fifo#(uvm_pcie::header))::get(m_sequencer, "" , "in_fifo", in_fifo)) begin
            `uvm_fatal(m_sequencer.get_full_name(), "\n\tuvm_pcie_axi::sequence cannot get in_fifo");
        end


        data.delete();
        state = PKT_NONE;

        // Because one low-level transaction can contains more
        // high-level transactions. Low level transaction
        // have to be count in middle of send_frame and get_response.
        // PEELING LOOP - Send first block
        gen = uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, tuser_width_get(ITEMS, AXI_CQ))::type_id::create("gen", m_sequencer);
        create_sequence_item(gen);
        req = gen;
        send_frame();

        while(transactions > 0 || data.size() > 0) begin
            // get response and check if tready is asserted
            gen = uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, tuser_width_get(ITEMS, AXI_CQ))::type_id::create("gen", m_sequencer);
            create_sequence_item(gen);

            get_response(rsp);
            while(req.tvalid == 1'b1 && rsp.tready == 1'b0) begin
                send_frame();
                get_response(rsp);
            end

            req = gen;
            send_frame();
        end

        // PEELING LOOP - Send last block
        get_response(rsp);
        while(req.tvalid == 1'b1 && rsp.tready == 1'b0) begin
            send_frame();
            get_response(rsp);
        end
    endtask
endclass



/////////////////////////////////////////////////////////////////////////
// SEQUENCE LIBRARY RX

class sequence_lib_cq #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    logic STRADDLING
) extends uvm_common::sequence_library#(
    config_sequence,
    uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, tuser_width_get(ITEMS, AXI_CQ))
);

  `uvm_object_param_utils(uvm_pcie_axi::sequence_lib_cq#(ITEMS, ITEM_WIDTH, STRADDLING))
  `uvm_sequence_library_utils(uvm_pcie_axi::sequence_lib_cq#(ITEMS, ITEM_WIDTH, STRADDLING))

  function new(string name = "sequence_lib_rx");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(uvm_pcie_axi::sequence_base_cq #(ITEMS, ITEM_WIDTH, STRADDLING)::get_type());
    endfunction
endclass

