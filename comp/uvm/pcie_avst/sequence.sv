//-- sequence.sv: Convert PCIE transaction to axi Trasnactions
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet>
//-- SPDX-License-Identifier: BSD-3-Clause


class sequence_down #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned META_WIDTH,
    int unsigned READY_LATENCY,
    logic STRADDLING
) extends uvm_common::sequence_base#(
    config_sequence,
    uvm_avst::sequence_item #(REGIONS, REGION_SIZE, 32, META_WIDTH)
);
    `ndk_object_param_utils(
        uvm_pcie_avst::sequence_down#(REGIONS, REGION_SIZE, META_WIDTH, READY_LATENCY, STRADDLING),
                            $sformatf("uvm_pcie_avst::sequence_down #(%0d,%0d,%0d,%0d,%0d)", REGIONS, REGION_SIZE,
                                      META_WIDTH, READY_LATENCY, STRADDLING)
    );
    `uvm_declare_p_sequencer(uvm_avst::sequencer #(REGIONS, REGION_SIZE, 32, META_WIDTH));

    localparam int unsigned ITEM_WIDTH = 32;

    int unsigned transactions_min = 10;
    int unsigned transactions_max = 300;
    rand int unsigned transactions;


    rand int unsigned rdy_probability_min;
    rand int unsigned rdy_probability_max;

    constraint c_transactions {
        transactions inside {[transactions_min:transactions_max]};
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

    typedef enum {PKT_NEW, PKT_HDR, PKT_DATA, PKT_SPACE} state_t;
    protected int unsigned    space;
    protected state_t         state;
    protected logic [32-1:0]  data[$];
    protected logic [128-1:0] hdr;
    protected logic [32-1:0]  prefix;
    protected logic [3-1:0]   bar;

    function new(string name = "uvm_pcie_avst::sequence_simple");
        super.new(name);
    endfunction

    function void item_done();
        data.delete();
    endfunction

    task send_empty_frame();
        start_item(req);
        assert(req.randomize() with {req.valid == '0;});
        finish_item(req);
        get_response(rsp);
    endtask


    task send_frame();
        // If reset then send empty frame
        if (p_sequencer.reset_sync.has_been_reset()) begin
            if (data.size() != 0) begin
                item_done();
            end

            req.randomize();
            req.valid = '0;
            state = PKT_SPACE;
            space = $urandom_range(0,20);
            cfg.rdy_latency = READY_LATENCY;
        end

        //SEND FRAME
        start_item(req);
        finish_item(req);
        get_response(rsp);

        if ((|req.valid) == 1'b1 && rsp.ready == 1'b0) begin
            if (cfg.rdy_latency != 0) begin
                cfg.rdy_latency--;
            end
        end

        while (cfg.rdy_latency == 0) begin
            send_empty_frame();
            if (rsp.ready == 1'b1) begin
                cfg.rdy_latency = READY_LATENCY;
            end
        end
    endtask

    task try_get(output uvm_pcie::header hdr);
        if (transactions != 0 && !p_sequencer.reset_sync.is_reset()) begin
            in_fifo.try_get(hdr);
        end else begin
            hdr = null;
        end
    endtask

    // gen.empty[it] = REGION_SIZE*BLOCK_SIZE - loop_end;
    virtual task create_sequence_item();
        int unsigned it = 0;

        void'(req.randomize()); // we need only random values
        req.valid = '0;

        if (state == PKT_SPACE) begin
            if (space > 0) begin
                space--;
                return;
            end else begin
                state = PKT_NEW;
            end
        end

        req.eop = 0;
        req.sop = 0;

        do begin
            if (state == PKT_NEW) begin
                uvm_pcie::header pcie_hdr;
                try_get(pcie_hdr);
                if (pcie_hdr != null) begin
                    logic [1-1:0] error = 0;
                    hdr_set(pcie_hdr, hdr, prefix, error, bar, data, cfg.bar);
                    state = PKT_DATA;

                    //SEND HEADER
                    req.sop[it]   = 1;
                    req.meta[it]  = {bar, prefix, hdr};
                end else begin
                    state = PKT_NEW;
                end
            end

            if (state == PKT_DATA) begin
                int unsigned jt = 0;

                req.valid[it] = 1;
                while (data.size() > 0 && jt < REGION_SIZE) begin
                    jt++;
                    req.data[it][jt*ITEM_WIDTH-1 -: ITEM_WIDTH] = data.pop_front();
                end

                if (data.size() == 0) begin
                    req.eop[it] = 1;
                    req.empty[it] = REGION_SIZE-jt;

                    state = ($urandom_range(3, 0) == 0) ? PKT_SPACE : PKT_NEW;
                    space = $urandom_range(0, 20);
                end
            end

            it++;
        end while(it < REGIONS && (data.size() != 0 || (req.eop[it-1] == 1 && STRADDLING == 1)));
    endtask

    task body;
        if(!uvm_config_db#(uvm_common::fifo#(uvm_pcie::header))::get(m_sequencer, "" , "in_fifo", in_fifo)) begin
            `uvm_fatal(m_sequencer.get_full_name(), "\n\tuvm_pcie_avst::sequence cannot get in_fifo");
        end

        data.delete();
        state = PKT_SPACE;
        space = 0;

        req = uvm_avst::sequence_item #(REGIONS, REGION_SIZE, 32, META_WIDTH)::type_id::create("req", m_sequencer);
        rsp = uvm_avst::sequence_item #(REGIONS, REGION_SIZE, 32, META_WIDTH)::type_id::create("rsp", m_sequencer);

        while(transactions > 0 || data.size() == 0) begin
            // get response and check if tready is asserted
            create_sequence_item();
            send_frame();
        end
    endtask
endclass



/////////////////////////////////////////////////////////////////////////
// SEQUENCE LIBRARY RX

class sequence_lib_down #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned META_WIDTH,
    int unsigned READY_LATENCY,
    logic STRADDLING
) extends uvm_common::sequence_library#(
    config_sequence,
    uvm_avst::sequence_item #(REGIONS, REGION_SIZE, 32, META_WIDTH)
);

  `ndk_object_param_utils(
        uvm_pcie_avst::sequence_lib_down#(REGIONS, REGION_SIZE, META_WIDTH, READY_LATENCY, STRADDLING),
        $sformatf("uvm_pcie_avst::sequence_lib_down #(%0d,%0d,%0d,%0d,%0d)", REGIONS, REGION_SIZE, META_WIDTH,
                  READY_LATENCY, STRADDLING)
    )
    `uvm_sequence_library_utils(
        uvm_pcie_avst::sequence_lib_down #(REGIONS, REGION_SIZE, META_WIDTH, READY_LATENCY, STRADDLING))

  function new(string name = "sequence_lib_rx");
    super.new(name);
    init_sequence_library();
  endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(
            uvm_pcie_avst::sequence_down #(REGIONS, REGION_SIZE, META_WIDTH, READY_LATENCY, STRADDLING)::get_type());
    endfunction
endclass

