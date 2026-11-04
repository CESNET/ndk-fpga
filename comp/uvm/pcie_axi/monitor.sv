// monitor.sv: pcie monitor
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

virtual class monitor#(
    int unsigned ITEMS,
    direction_t DIR,
    string DEVICE = "ULTRASCALE"
) extends uvm_pcie::monitor;

    // LOCAL PARAMETERS
    localparam ITEM_WIDTH = 32; //as all pcie devices
    localparam TUSER_WIDTH = tuser_width_get(ITEMS, DIR, DEVICE);
    // Positions of the tuser fields
    localparam tuser_layout_t LAYOUT = tuser_layout_get(ITEMS, DIR);
    localparam int unsigned PACKET_MAX = LAYOUT.slots;
    localparam int unsigned SOF_INDEX  = LAYOUT.sop;
    localparam int unsigned SOF_PTR_W  = LAYOUT.sop_ptr_w;
    localparam int unsigned SOF_UNIT   = LAYOUT.sop_unit;
    localparam int unsigned EOF_INDEX  = LAYOUT.eop;
    localparam int unsigned EOF_PTR_W  = LAYOUT.eop_ptr_w;
    localparam int unsigned FBE_INDEX  = LAYOUT.fbe;
    localparam int unsigned LBE_INDEX  = LAYOUT.lbe;

    typedef monitor#(ITEMS, DIR, DEVICE) this_type;
    uvm_analysis_imp#(uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH), this_type) port_axi;

    // protected variable
    protected logic [ITEM_WIDTH-1:0] data[$];
    protected time                   time_start;
    protected time                   time_end;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        port_axi = new("port_axi", this);
    endfunction

    function void read_data(ref logic [ITEMS*ITEM_WIDTH-1:0] in_data, input int unsigned start, int unsigned stop);
        for (int unsigned it = start; it < stop; it++) begin
            data.push_back(in_data[(it+1)*ITEM_WIDTH-1 -: ITEM_WIDTH]);
        end
    endfunction

    // Report a beat with TVALID set and TREADY unknown out of the reset.
    // Such a beat is not a handshake for the monitor nor for the CQ/RC sequences.
    function void handshake_x_check(uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) t);
        if (t.tvalid === 1'b1 && $isunknown(t.tready) && !reset_sync.is_reset()) begin
            `uvm_error(this.get_full_name(), $sformatf(
                       "\n\tTREADY is 0b%b while TVALID is set at %0t", t.tready, t.time_last()));
        end
    endfunction

    // The header must be a memory read/write and a CQ packet must contain exactly
    // its payload. Otherwise the monitor lost a beat (it is out of sync with the driver).
    function void req_check();
        logic [4-1:0]  req_type    = 'x;
        logic [11-1:0] dword_count = 'x;
        int unsigned   exp_size    = 0;
        string         dws         = "";

        // The request type and the dword count have the same positions
        // in the CQ and RQ descriptors
        if (data.size() >= 4) begin
            req_type    = data[2][15-1:11];
            dword_count = data[2][11-1:0];
            exp_size    = 4;
            if (req_type == 4'b0001) begin
                exp_size += (dword_count != 0) ? dword_count : 1024;
            end
        end

        if (data.size() < 4 || !(req_type inside {4'b0000, 4'b0001}) ||
            (DIR == AXI_CQ && data.size() != exp_size)) begin
            for (int unsigned it = 0; it < data.size() && it < 16; it++) begin
                dws = {dws, $sformatf(" 'h%h", data[it])};
            end
            `uvm_fatal(this.get_full_name(), $sformatf({
                "\n\tBroken request (start %0t, end %0t): %0d DWs,",
                " request type 0b%b, dword count %0d",
                "\n\tThe first DWs:%s",
                "\n\tProbably a lost beat or a packet started during the reset"},
                time_start, time_end, data.size(), req_type, dword_count, dws));
        end
    endfunction

    function void send_req(logic [4-1:0] fbe, logic [4-1:0] lbe);
        uvm_pcie::request_header hdr;

        req_check();

        if (DIR == AXI_RQ) begin
            hdr = hdr_rq_get(data, fbe, lbe);
        end else if (DIR == AXI_CQ) begin
            hdr = hdr_cq_get(data, fbe, lbe, bar_cfg);
        end else begin
            `uvm_fatal(this.get_full_name(), "\nUnknown request header");
        end

        hdr.start[{this.get_full_name(), "_start"}] = time_start;
        hdr.start[{this.get_full_name(), "_end"}]   = time_end;
        data.delete();
        analysis_port.write(hdr);
    endfunction

    function void send_comp();
        uvm_pcie::completer_header hdr;

        if (DIR == AXI_RC) begin
            hdr = hdr_rc_get(data);
        end else if (DIR == AXI_CC) begin
            hdr = hdr_cc_get(data);
        end else begin
            `uvm_fatal(this.get_full_name(), "\nUnknown request header");
        end

        hdr.start[{this.get_full_name(), "_start"}] = time_start;
        hdr.start[{this.get_full_name(), "_end"}]   = time_end;
        data.delete();
        analysis_port.write(hdr);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
    endfunction

    virtual function void write(uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) t);
    endfunction
endclass



class monitor_CC #(
    int unsigned ITEMS,
    logic STRADDLING,
    string DEVICE = "ULTRASCALE"
) extends monitor#(ITEMS, AXI_CC, DEVICE);
    `ndk_component_param_utils(
        uvm_pcie_axi::monitor_CC#(ITEMS, STRADDLING, DEVICE),
        $sformatf("uvm_pcie_axi::monitor_CC#(%0d,%0d,%s)",ITEMS, STRADDLING, DEVICE)
    );

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        assert(STRADDLING == 0 || ITEMS >= 16) else begin
            `uvm_fatal(this.get_full_name(), $sformatf(
                       "\n\tUnsupported combination of DATA_WIDTH(%0d) and STRADDLING(%0d)", ITEMS * 32, STRADDLING));
        end
    endfunction

    virtual function void write(uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) t);
        int unsigned sof_num; // which sof index is next
        int unsigned eof_num; // which eof index is next
        logic [PACKET_MAX+1-1:0] sof_vld;
        logic [PACKET_MAX-1:0] eof_vld;
        int unsigned sof[PACKET_MAX+1];
        int unsigned eof[PACKET_MAX];
        int unsigned it = 0;

        // If reset ocurres then reset all data
        if (reset_sync.has_been_reset()) begin
            data.delete();
        end

        // No valid data are present
        if (t.tvalid === 1'b0 || t.tready === 1'b0 || reset_sync.is_reset()) begin
            return;
        end

        sof_num = 0;
        eof_num = 0;
        // when data size then this is out of frame
        if (STRADDLING == 1) begin
            if (data.size() > 0) begin
                //setup first start from zero
                sof_vld = {t.tuser[PACKET_MAX+SOF_INDEX-1 -: PACKET_MAX], 1'b1};
                sof[0]   = 0;
                //GET ALL SOF
                for (int unsigned it = 0; it < PACKET_MAX; it++) begin
                    sof[it+1] = t.tuser[(it+1)*SOF_PTR_W+PACKET_MAX+SOF_INDEX-1 -: SOF_PTR_W];
                end

            end else begin
                sof_vld = {1'b0, t.tuser[PACKET_MAX+SOF_INDEX-1 -: PACKET_MAX]};
                //GET ALL SOF
                for (int unsigned it = 0; it < PACKET_MAX; it++) begin
                    sof[it] = t.tuser[(it+1)*SOF_PTR_W+PACKET_MAX+SOF_INDEX-1 -: SOF_PTR_W];
                end
            end

            eof_vld = t.tuser[PACKET_MAX+EOF_INDEX-1 -: PACKET_MAX];
            for (int unsigned it = 0; it < PACKET_MAX; it++) begin
                //pointer right behinde array
                eof[it] = t.tuser[(it+1)*EOF_PTR_W+PACKET_MAX+EOF_INDEX-1 -: EOF_PTR_W] + 1;
            end

            assert(!(data.size() > 0 && sof_vld[0] == 1 && sof[0] != 0)) else begin
                `uvm_fatal(this.get_full_name(),
                           "\nPacket can start in REGION only if previous region packet stop or it is first region!!!")
            end
        end else begin
            sof_vld = 1'b1;
            sof[0]  = 0;
            eof_vld = t.tlast;
            // here should be binary search
            eof[0] = ITEMS;
            while (eof[0] > 1 && !t.tkeep[eof[0]-1]) begin
                eof[0]--;
            end

            assert(t.tlast == 1'b1 || t.tkeep[ITEMS-1] == 1'b1) else begin
                `uvm_error(this.get_full_name(), $sformatf(
                           "\n\tBroken protocol axi protocol !!!\n\tTkeep have to be all ones if tlast is not set"));
           end
        end

        while (sof_num <= PACKET_MAX && sof_vld[sof_num] == 1) begin

            // If there would be start of packet, update start_time
            // dont udate if packet continue in this beat
            if (data.size() == 0) begin
                time_start = t.time_last();
            end

            //get eof
            if (eof_num < PACKET_MAX && eof_vld[eof_num] == 1) begin
                read_data(t.tdata, sof[sof_num]*SOF_UNIT, eof[eof_num]);
                time_end = t.time_last();
                send_comp();
                eof_num++;
            end else begin
                read_data(t.tdata, sof[sof_num]*SOF_UNIT, ITEMS);
            end

            sof_num++;
        end
    endfunction
endclass

class monitor_CQ #(
    int unsigned ITEMS,
    logic STRADDLING,
    string DEVICE = "ULTRASCALE"
) extends monitor#(ITEMS, AXI_CQ, DEVICE);
    `ndk_component_param_utils(
        uvm_pcie_axi::monitor_CQ#(ITEMS, STRADDLING, DEVICE),
        $sformatf("uvm_pcie_axi::monitor_CQ#(%0d,%0d,%s)",ITEMS, STRADDLING, DEVICE)
    );

    protected logic [4-1:0] fbe;
    protected logic [4-1:0] lbe;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        assert(STRADDLING == 0 || ITEMS >= 16) else begin
            `uvm_fatal(this.get_full_name(), $sformatf(
                       "\n\tUnsupported combination of DATA_WIDTH(%0d) and STRADDLING(%0d)", ITEMS * 32, STRADDLING));
        end
    endfunction

    virtual function void write(uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) t);
        int unsigned be_num; // which sof index is next
        int unsigned sof_num; // which sof index is next
        int unsigned eof_num; // which eof index is next
        logic [PACKET_MAX+1-1:0] sof_vld;
        logic [PACKET_MAX-1:0] eof_vld;
        int unsigned sof[PACKET_MAX+1];
        int unsigned eof[PACKET_MAX];
        int unsigned it = 0;

        // If reset ocurres then reset all data
        if (reset_sync.has_been_reset()) begin
            data.delete();
        end

        handshake_x_check(t);
        if ($isunknown(t.tvalid) || $isunknown(t.tready)) begin
            return;
        end

        // No valid data are present
        if (t.tvalid === 1'b0 || t.tready === 1'b0 || reset_sync.is_reset()) begin
            return;
        end

        sof_num = 0;
        eof_num = 0;
        be_num  = 0;
        // when data size then this is out of frame
        if (STRADDLING == 1) begin
            if (data.size() > 0) begin
                //setup first start from zero
                sof_vld = {t.tuser[PACKET_MAX+SOF_INDEX-1 -: PACKET_MAX], 1'b1};
                sof[0]   = 0;
                //GET ALL SOF
                for (int unsigned it = 0; it < PACKET_MAX; it++) begin
                    sof[it+1] = t.tuser[(it+1)*SOF_PTR_W+PACKET_MAX+SOF_INDEX-1 -: SOF_PTR_W];
                end

            end else begin
                sof_vld = {1'b0, t.tuser[PACKET_MAX+SOF_INDEX-1 -: PACKET_MAX]};
                //GET ALL SOF
                for (int unsigned it = 0; it < PACKET_MAX; it++) begin
                    sof[it] = t.tuser[(it+1)*SOF_PTR_W+PACKET_MAX+SOF_INDEX-1 -: SOF_PTR_W];
                end
            end

            eof_vld = t.tuser[PACKET_MAX+EOF_INDEX-1 -: PACKET_MAX];
            for (int unsigned it = 0; it < PACKET_MAX; it++) begin
                //pointer right behinde array
                eof[it] = t.tuser[(it+1)*EOF_PTR_W+PACKET_MAX+EOF_INDEX-1 -: EOF_PTR_W] + 1;
            end

            assert(!(data.size() > 0 && sof_vld[0] == 1 && sof[0] != 0)) else begin
                `uvm_fatal(this.get_full_name(), "This is not supported combination!!!")
            end
        end else begin
            sof_vld = 1'b1;
            sof[0]  = 0;
            eof_vld = t.tlast;
            // here should be binary search
            eof[0] = ITEMS;
            while (eof[0] > 1 && !t.tkeep[eof[0]-1]) begin
                eof[0]--;
            end

            assert(t.tlast == 1'b1 || t.tkeep[ITEMS-1] == 1'b1) else begin
                `uvm_error(this.get_full_name(), $sformatf(
                           "\n\tBroken protocol axi protocol !!!\n\tTkeep have to be all ones if tlast is not set\n%s",
                           t.convert2string()
                           ));
           end
        end

        while (sof_num <= PACKET_MAX && sof_vld[sof_num] == 1) begin

            // If there would be start of packet, update start_time
            // dont udate if packet continue in this beat
            if (data.size() == 0) begin // if data.size == 0 this means new packet
                fbe = t.tuser[(be_num+1)*4 + FBE_INDEX-1 -:4];
                lbe = t.tuser[(be_num+1)*4 + LBE_INDEX-1 -:4];

                be_num++;
                time_start = t.time_last();
            end

            //get eof
            if (eof_num < PACKET_MAX && eof_vld[eof_num] == 1) begin
                read_data(t.tdata, sof[sof_num]*SOF_UNIT, eof[eof_num]);
                time_end = t.time_last();
                send_req(fbe, lbe);
                eof_num++;
            end else begin
                read_data(t.tdata, sof[sof_num]*SOF_UNIT, ITEMS);
            end

            sof_num++;
        end
    endfunction
endclass

class monitor_RQ #(
    int unsigned ITEMS,
    logic STRADDLING,
    string DEVICE = "ULTRASCALE"
) extends monitor#(ITEMS, AXI_RQ, DEVICE);
    `ndk_component_param_utils(
        uvm_pcie_axi::monitor_RQ#(ITEMS, STRADDLING, DEVICE),
        $sformatf("uvm_pcie_axi::monitor_RQ#(%0d,%0d,%s)",ITEMS, STRADDLING, DEVICE)
    );

    protected logic [4-1:0] fbe;
    protected logic [4-1:0] lbe;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        // STRADDLING is supported only when ITES is 16
        assert(STRADDLING == 0 || ITEMS >= 16) else begin
            `uvm_fatal(this.get_full_name(), $sformatf(
                       "\n\tUnsupported combination of DATA_WIDTH(%0d) and STRADDLING(%0d)", ITEMS * 32, STRADDLING));
        end
    endfunction

    virtual function void write(uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) t);
        int unsigned sof_num; // which sof index is next
        int unsigned eof_num; // which eof index is next
        int unsigned be_num; // which sof index is next
        logic [PACKET_MAX+1-1:0] sof_vld;
        logic [PACKET_MAX-1:0] eof_vld;
        int unsigned sof[PACKET_MAX+1];
        int unsigned eof[PACKET_MAX];
        int unsigned it = 0;

        // If reset ocurres then reset all data
        if (reset_sync.has_been_reset()) begin
            data.delete();
        end

        // No valid data are present
        if (t.tvalid === 1'b0 || t.tready === 1'b0 || reset_sync.is_reset()) begin
            return;
        end

        sof_num = 0;
        eof_num = 0;
        be_num  = 0;

        // decision if we use stradling or not
        if (STRADDLING == 1) begin

            // When packet is transmissed then
            // set start position to 0
            if (data.size() > 0) begin
                //setup first start from zero
                sof_vld = {t.tuser[PACKET_MAX+SOF_INDEX-1 -: PACKET_MAX], 1'b1};
                sof[0]   = 0;
                //GET ALL SOF
                for (int unsigned it = 0; it < PACKET_MAX; it++) begin
                    sof[it+1] = t.tuser[(it+1)*SOF_PTR_W+PACKET_MAX+SOF_INDEX-1 -: SOF_PTR_W];
                end

            // When packet is not transmissed then
            // set start position to on sof_ptr[0]
            end else begin
                sof_vld = {1'b0, t.tuser[PACKET_MAX+SOF_INDEX-1 -: PACKET_MAX]};
                //GET ALL SOF
                for (int unsigned it = 0; it < PACKET_MAX; it++) begin
                    sof[it] = t.tuser[(it+1)*SOF_PTR_W+PACKET_MAX+SOF_INDEX-1 -: SOF_PTR_W];
                end
            end

            eof_vld = t.tuser[PACKET_MAX+EOF_INDEX-1 -: PACKET_MAX];
            for (int unsigned it = 0; it < PACKET_MAX; it++) begin
                //pointer right behinde array
                eof[it] = t.tuser[(it+1)*EOF_PTR_W+PACKET_MAX+EOF_INDEX-1 -: EOF_PTR_W] + 1;
            end

            assert(!(data.size() > 0 && sof_vld[0] == 1 && sof[0] != 0)) else begin
                `uvm_fatal(this.get_full_name(), "This is not supported combination!!!")
            end

        // Get sof and eof withnout straddling
        end else begin
            sof_vld = 1'b1;
            sof[0]  = 0;
            eof_vld = t.tlast;
            // TODO: here should be binary search
            eof[0] = ITEMS;
            while (eof[0] > 1 && !t.tkeep[eof[0]-1]) begin
                eof[0]--;
            end

            assert(t.tlast == 1'b1 || t.tkeep[ITEMS-1] == 1'b1) else begin
                `uvm_error(this.get_full_name(), $sformatf(
                           "\n\tBroken protocol axi protocol !!!\n\tTkeep have to be all ones if tlast is not set"));
           end
        end

        while (sof_num <= PACKET_MAX && sof_vld[sof_num] == 1) begin

            // If there would be start of packet, update start_time
            // dont udate if packet continue in this beat
            // If there would be start of packet, update start_time
            // dont udate if packet continue in this beat
            if (data.size() == 0) begin
                fbe = t.tuser[(be_num+1)*4 + FBE_INDEX-1 -:4];
                lbe = t.tuser[(be_num+1)*4 + LBE_INDEX-1 -:4];
                time_start = t.time_last();

                be_num++;
            end

            //get eof
            if (eof_num < PACKET_MAX && eof_vld[eof_num] == 1) begin
                read_data(t.tdata, sof[sof_num]*SOF_UNIT, eof[eof_num]);
                time_end = t.time_last();
                send_req(fbe, lbe);
                eof_num++;
            end else begin
                read_data(t.tdata, sof[sof_num]*SOF_UNIT, ITEMS);
            end

            sof_num++;
        end
    endfunction
endclass

class monitor_RC #(
    int unsigned ITEMS,
    logic STRADDLING,
    string DEVICE = "ULTRASCALE"
) extends monitor#(ITEMS, AXI_RC, DEVICE);
    `ndk_component_param_utils(
        uvm_pcie_axi::monitor_RC#(ITEMS, STRADDLING, DEVICE),
        $sformatf("uvm_pcie_axi::monitor_RC#(%0d,%0d,%s)",ITEMS, STRADDLING, DEVICE)
    )

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        assert(STRADDLING == 0 || ITEMS >= 16) else begin
            `uvm_fatal(this.get_full_name(), $sformatf(
                       "\n\tUnsupported combination of DATA_WIDTH(%0d) and STRADDLING(%0d)", ITEMS * 32, STRADDLING));
        end
    endfunction

    virtual function void write(uvm_axi::sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) t);
        int unsigned sof_num; // which sof index is next
        int unsigned eof_num; // which eof index is next
        logic [PACKET_MAX+1-1:0] sof_vld;
        logic [PACKET_MAX-1:0] eof_vld;
        int unsigned sof[PACKET_MAX+1];
        int unsigned eof[PACKET_MAX];
        int unsigned it = 0;

        // If reset ocurres then reset all data
        if (reset_sync.has_been_reset()) begin
            data.delete();
        end

        handshake_x_check(t);
        if ($isunknown(t.tvalid) || $isunknown(t.tready)) begin
            return;
        end

        // No valid data are present
        if (t.tvalid == 1'b0 || t.tready == 1'b0 || reset_sync.is_reset()) begin
            return;
        end

        sof_num = 0;
        eof_num = 0;
        // when data size then this is out of frame
        if (STRADDLING == 1) begin
            if (data.size() > 0) begin
                //setup first start from zero
                sof_vld = {t.tuser[PACKET_MAX+SOF_INDEX-1 -: PACKET_MAX], 1'b1};
                sof[0]   = 0;
                //GET ALL SOF
                for (int unsigned it = 0; it < PACKET_MAX; it++) begin
                    sof[it+1] = t.tuser[(it+1)*SOF_PTR_W+PACKET_MAX+SOF_INDEX-1 -: SOF_PTR_W];
                end

            end else begin
                sof_vld = {1'b0, t.tuser[PACKET_MAX+SOF_INDEX-1 -: PACKET_MAX]};
                //GET ALL SOF
                for (int unsigned it = 0; it < PACKET_MAX; it++) begin
                    sof[it] = t.tuser[(it+1)*SOF_PTR_W+PACKET_MAX+SOF_INDEX-1 -: SOF_PTR_W];
                end
            end

            eof_vld = t.tuser[PACKET_MAX+EOF_INDEX-1 -: PACKET_MAX];
            for (int unsigned it = 0; it < PACKET_MAX; it++) begin
                //pointer right behinde array
                eof[it] = t.tuser[(it+1)*EOF_PTR_W+PACKET_MAX+EOF_INDEX-1 -: EOF_PTR_W] + 1;
            end

            assert(!(data.size() > 0 && sof_vld[0] == 1 && sof[0] != 0)) else begin
                `uvm_fatal(this.get_full_name(), "This is not supported combination!!!")
            end
        end else begin
            sof_vld = 1'b1;
            sof[0]  = 0;
            eof_vld = t.tlast;
            // here should be binary search
            eof[0] = ITEMS;
            while (eof[0] > 1 && !t.tkeep[eof[0]-1]) begin
                eof[0]--;
            end

            assert(t.tlast == 1'b1 || t.tkeep[ITEMS-1] == 1'b1) else begin
                `uvm_error(this.get_full_name(), $sformatf(
                           "\n\tBroken protocol axi protocol !!!\n\tTkeep ('b%b) have to be all ones if tlast('b%b) is not set"
                               ,
                           t.tkeep,
                           t.tlast
                           ));
            end
        end

        while (sof_num <= PACKET_MAX && sof_vld[sof_num] == 1) begin

            // If there would be start of packet, update start_time
            // dont udate if packet continue in this beat
            if (data.size() == 0) begin
                time_start = t.time_last();
            end

            //get eof
            if (eof_num < PACKET_MAX && eof_vld[eof_num] == 1) begin
                read_data(t.tdata, sof[sof_num]*SOF_UNIT, eof[eof_num]);
                time_end = t.time_last();
                send_comp();
                eof_num++;
            end else begin
                read_data(t.tdata, sof[sof_num]*SOF_UNIT, ITEMS);
            end

            sof_num++;
        end

        //`uvm_fatal(this.get_full_name(), $sformatf("\n\tThis Monitor is not implemented!!!\n"));
    endfunction
endclass


class monitor_register #(int unsigned ITEMS, direction_t DIR, logic STRADDLING, string DEVICE = "ULTRASCALE");
    static function uvm_object_wrapper get();
        automatic uvm_object_wrapper ret = null;

        if (ITEMS == 2 || ITEMS == 4 || ITEMS == 8 || ITEMS == 16 || ITEMS == 32) begin
            unique case (DIR)
                AXI_RQ: ret = monitor_RQ#(ITEMS, STRADDLING, DEVICE)::get_type();
                AXI_RC: ret = monitor_RC#(ITEMS, STRADDLING, DEVICE)::get_type();
                AXI_CQ: ret = monitor_CQ#(ITEMS, STRADDLING, DEVICE)::get_type();
                AXI_CC: ret = monitor_CC#(ITEMS, STRADDLING, DEVICE)::get_type();
            endcase
        end else begin
            $error("Unsupported number of items %0d\nSUPPORTED VALUES [2, 4, 8, 16, 32]\n", ITEMS);
        end

        return ret;
    endfunction
endclass
