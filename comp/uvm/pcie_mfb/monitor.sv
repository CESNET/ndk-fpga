// monitor.sv: pcie monitor
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class monitor_rx #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    direction_t  DIR,
    meta_position_t META_TYPE,
    device_t DEVICE
) extends uvm_pcie::monitor;

    `ndk_component_param_utils(
        uvm_pcie_mfb::monitor_rx#(REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, META_TYPE, DEVICE),
        $sformatf("uvm_pcie_mfb::monitor_rx#(%0d,%0d,%0d,%s,%s,%s)",
            REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, META_TYPE, DEVICE
        )
    );

    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(32))                    port_data;
    uvm_tlm_analysis_fifo#(uvm_logic_vector::sequence_item#(meta_width_get(DIR, DEVICE))) port_meta;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        port_data = new("port_data", this);
        port_meta = new("port_meta", this);
    endfunction

    task run_phase(uvm_phase phase);

        forever begin
            uvm_pcie::header                                       hdr;
            uvm_logic_vector_array::sequence_item #(32)            data;
            uvm_logic_vector::sequence_item #(meta_width_get(DIR, DEVICE)) meta;

            port_data.get(data);
            port_meta.get(meta);

            // XILINX DEVICE
            if (DEVICE == DEV_XILINX) begin
                if (DIR == MFB_RQ) begin
                    // 166:166 - fbe, 170:167 - lbe
                    hdr = uvm_pcie_axi::hdr_rq_get(data.data, meta.data[163:160], meta.data[167:164]);
                end else if (DIR == MFB_CC) begin
                    hdr = uvm_pcie_axi::hdr_cc_get(data.data);
                end else begin
                    `uvm_fatal(this.get_full_name(), "\n\t THIS IS NOT IMPLEMENTED -- CREATE PCIE FROM MFB and MVB");
                end

            end else if (DEVICE == DEV_INTEL) begin
                logic [128-1:0] meta_hdr;
                logic [32-1:0]  meta_prefix;
                logic [3-1:0]   bar;
                logic [1-1:0]   error;

                if (DIR == MFB_RQ) begin
                    bar = 0;
                    error = 0;
                    {meta_prefix, meta_hdr} = meta.data[160-1:0];
                end else if (DIR == MFB_CC) begin
                    bar = 0;
                    error = 0;
                    meta_hdr = 0;
                    {meta_prefix, meta_hdr[96-1:0]} = meta.data[128-1:0];
                end else if (DIR == MFB_RC) begin
                    bar = 0;
                    error = 0;
                    meta_hdr = 0;
                    {meta_prefix, meta_hdr[96-1:0]} = meta.data[128-1:0];
                end else begin
                    `uvm_fatal(this.get_full_name(), "\n\t THIS IS NOT IMPLEMENTED -- CREATE PCIE FROM MFB and MVB");
                end

                //Be carefull DWORD ORDER - more info P-TILE intel
                hdr = uvm_pcie_avst::hdr_get({ <<32 {meta_hdr}}, meta_prefix, error, bar, data.data, bar_cfg, this);
            end else begin
                `uvm_fatal(this.get_full_name(), "\n\tUNSUPPORTED DEVICE\n");
            end

            hdr.time_array_add(data.start);
            hdr.time_array_add(meta.start);
            analysis_port.write(hdr);
        end
    endtask
endclass



`uvm_analysis_imp_decl(_mvb)
`uvm_analysis_imp_decl(_mfb)

class monitor #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    direction_t  DIR,
    meta_position_t META_TYPE,
    device_t DEVICE
) extends uvm_pcie::monitor;

    `ndk_component_param_utils(
        uvm_pcie_mfb::monitor#(REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, META_TYPE, DEVICE),
        $sformatf("uvm_pcie_mfb::monitor#(%0d,%0d,%0d,%s,%s,%s)",
            REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, META_TYPE, DEVICE
        )
    );

    // LOCAL PARAMETERS
    localparam ITEM_WIDTH = 32; //as all pcie devices
    localparam META_WIDTH = meta_width_get(DIR, DEVICE);
    localparam MFB_META_WIDTH = (META_TYPE != MFB_META_NONE) ? META_WIDTH : 0;

    typedef monitor#(REGIONS, REGION_SIZE, BLOCK_SIZE, DIR, META_TYPE, DEVICE) this_type;
    uvm_analysis_imp_mfb#(
        uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MFB_META_WIDTH), this_type
    ) port_mfb;
    uvm_analysis_imp_mvb#(
        uvm_mvb::sequence_item #(REGIONS, META_WIDTH), this_type
    ) port_mvb;

    // TOP LEVEL
    // protected variable
    protected time                   mfb_time[$];
    protected logic [ITEM_WIDTH-1:0] mfb_fifo[$][];
    protected logic [META_WIDTH-1:0] mvb_fifo[$];

    //lower level
    protected logic [ITEM_WIDTH-1:0] mfb_data[$];

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        port_mfb = new("port_mfb", this);
        port_mvb = new("port_mvb", this);
    endfunction

    function void read_data(
            ref logic [REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1:0] in_data,
            input int unsigned start,
            int unsigned stop
        );

        for (int unsigned it = start; it < stop; it++) begin
            mfb_data.push_back(in_data[(it+1)*ITEM_WIDTH-1 -: ITEM_WIDTH]);
        end
    endfunction

    function void send_data();
        mfb_fifo.push_back(mfb_data);
        mfb_data.delete();
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
    endfunction

    virtual function void reset();
        mfb_data.delete();
        mfb_fifo.delete();
        mvb_fifo.delete();
    endfunction

    virtual function void write_mfb(
            uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MFB_META_WIDTH) t
        );

        // No valid data are present
        if (reset_sync.has_been_reset()) begin
            reset();
        end

        if (t.src_rdy === 1'b0 || t.dst_rdy === 1'b0) begin
            return;
        end

        for (int unsigned it = 0; it < REGIONS; it++) begin
            // check if we are inframe
            if (mfb_data.size() > 0) begin
                if (t.eof[it] == 1'b1) begin
                    read_data(t.data[it], 0, t.eof_pos[it]+1);
                    if (META_TYPE == MFB_META_EOF) begin
                        mvb_fifo.push_back(t.meta[it]);
                    end
                    send_data();
                end else begin
                    read_data(t.data[it], 0, REGION_SIZE * BLOCK_SIZE);
                end
            end

            // There is start of packet
            if (t.sof[it] == 1'b1) begin
                int unsigned sof_pos;

                if ($clog2(REGION_SIZE) != 0) begin
                    sof_pos = 0;
                end else begin
                    sof_pos = BLOCK_SIZE*t.sof_pos[it];
                end

                mfb_time.push_back($time);
                if (META_TYPE == MFB_META_SOF) begin
                    mvb_fifo.push_back(t.meta[it]);
                end

                // Packet start and end in this region
                if (t.eof[it] == 1 && t.eof_pos[it] >= sof_pos) begin
                    read_data(t.data[it], sof_pos, t.eof_pos[it]+1);
                    if (META_TYPE == MFB_META_EOF) begin
                        mvb_fifo.push_back(t.meta[it]);
                    end
                    send_data();
                end else begin
                    read_data(t.data[it], sof_pos, REGION_SIZE * BLOCK_SIZE);
                end
            end
        end
    endfunction

    virtual function void write_mvb(uvm_mvb::sequence_item #(REGIONS, META_WIDTH) t);

        if (reset_sync.has_been_reset()) begin
            reset();
        end

        if (t.src_rdy === 1'b0 || t.dst_rdy === 1'b0 || META_TYPE != MFB_META_NONE) begin
            return;
        end

        for (int unsigned it = 0; it < REGIONS; it++) begin
            if (t.vld[it] == 1'b1) begin
                mvb_fifo.push_back(t.data[it]);
            end
        end
    endfunction

    task run_phase(uvm_phase phase);

        forever begin
            uvm_pcie::header hdr;
            logic [ITEM_WIDTH-1:0] tmp_mfb[];
            logic [META_WIDTH-1:0] tmp_mvb;
            time                   start;

            wait(mfb_fifo.size() > 0 &&  mvb_fifo.size() > 0);

            // If reset ocurres then reset all data
            tmp_mfb = mfb_fifo.pop_front();
            start   = mfb_time.pop_front();
            tmp_mvb = mvb_fifo.pop_front();

            if (DEVICE == DEV_XILINX) begin
                if (DIR ==  MFB_CQ) begin
                    hdr = uvm_pcie_axi::hdr_cq_get(tmp_mfb, tmp_mvb[166:163], tmp_mvb[170:167], bar_cfg);
                end else if (DIR ==  MFB_RQ) begin
                    hdr = uvm_pcie_axi::hdr_rq_get(tmp_mfb, tmp_mvb[164-1:160], tmp_mvb[168-1:164]);
                end else if (DIR ==  MFB_RC) begin
                    hdr = uvm_pcie_axi::hdr_rc_get(tmp_mfb);
                end
            end else if (DEVICE == DEV_INTEL) begin
                logic [128-1:0] header;
                logic [32-1:0]  prefix;
                logic [3-1:0]   bar;
                logic [1-1:0]   error;

                if (DIR ==  MFB_CQ) begin
                    error = 0;
                    {bar, prefix, header} = tmp_mvb[163-1:0];
                end else if (DIR ==  MFB_RQ) begin
                    error  = 0;
                    bar    = 0;
                    {prefix, header} = tmp_mvb[160-1:0];
                end else if (DIR ==  MFB_RC) begin
                    error = 0;
                    bar = 0;
                    header = 0;
                    {prefix, header[96-1:0]} = tmp_mvb[128-1:0];
                end

                hdr = uvm_pcie_avst::hdr_get({ <<32{header}}, prefix, error, bar, tmp_mfb, bar_cfg, this);
            end else begin
                `uvm_fatal(this.get_full_name(), "\n\t THIS IS NOT IMPLEMENTED -- CREATE PCIE FROM MFB and MVB");
            end

            hdr.start[this.get_full_name()] = start;
            analysis_port.write(hdr);
        end
    endtask
endclass

