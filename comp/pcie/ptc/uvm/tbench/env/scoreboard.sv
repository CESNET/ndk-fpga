//-- scoreboard.sv: Scoreboard for verification
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class up_catch extends uvm_component;
    `uvm_component_utils(uvm_ptc::up_catch)

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item#(32))                         up_mfb_gen;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(sv_dma_bus_pack::DMA_UPHDR_WIDTH)) up_mvb_gen;

    uvm_logic_vector_array::sequence_item #(32)                         dut_up_mfb_array [logic [8-1 : 0]];
    uvm_logic_vector::sequence_item #(sv_dma_bus_pack::DMA_UPHDR_WIDTH) dut_up_mvb_array [logic [8-1 : 0]];
    int unsigned up_mfb_cnt;
    int unsigned up_mvb_cnt;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        up_mfb_gen = new("up_mfb_gen", this);
        up_mvb_gen = new("up_mvb_gen", this);
        up_mfb_cnt = 0;
        up_mvb_cnt = 0;
    endfunction

    task run_phase(uvm_phase phase);

        uvm_logic_vector_array::sequence_item#(32)                         tr_up_mfb_gen;
        uvm_logic_vector::sequence_item#(sv_dma_bus_pack::DMA_UPHDR_WIDTH) tr_up_mvb_gen;

        forever begin
            string msg;
            string debug_msg = "";

            up_mvb_gen.get(tr_up_mvb_gen);
            up_mvb_cnt++;

            if (tr_up_mvb_gen.data[sv_dma_bus_pack::DMA_REQUEST_FIRSTIB_O-1 : sv_dma_bus_pack::DMA_REQUEST_TYPE_O] == 1'b1) begin
                up_mfb_gen.get(tr_up_mfb_gen);
                up_mfb_cnt++;
            end

            debug_msg = {debug_msg, $sformatf("\n\t GEN UP MVB TR NUMBER: %d: %s\n",  up_mvb_cnt, tr_up_mvb_gen.convert2string())};
            if (tr_up_mfb_gen != null) begin
                debug_msg = {debug_msg, $sformatf("\n\t GEN UP MFB TR NUMBER: %d: %s\n",  up_mfb_cnt, tr_up_mfb_gen.convert2string())};
            end
            `uvm_info(this.get_full_name(), debug_msg ,UVM_FULL);

            // IF READ REQ, load the UP request
            if (tr_up_mvb_gen.data[sv_dma_bus_pack::DMA_REQUEST_FIRSTIB_O-1 : sv_dma_bus_pack::DMA_REQUEST_TYPE_O] == 1'b0) begin
                if (dut_up_mvb_array.exists(tr_up_mvb_gen.data[sv_dma_bus_pack::DMA_REQUEST_UNITID_O-1 : sv_dma_bus_pack::DMA_REQUEST_TAG_O])) begin
                    $write("FATAL TAG: %h\n", tr_up_mvb_gen.data[sv_dma_bus_pack::DMA_REQUEST_UNITID_O-1 : sv_dma_bus_pack::DMA_REQUEST_TAG_O]);
                    `uvm_fatal(this.get_full_name(), "Transaction exists");
                end else begin
                    dut_up_mfb_array[tr_up_mvb_gen.data[sv_dma_bus_pack::DMA_REQUEST_UNITID_O-1 : sv_dma_bus_pack::DMA_REQUEST_TAG_O]] = tr_up_mfb_gen;
                    dut_up_mvb_array[tr_up_mvb_gen.data[sv_dma_bus_pack::DMA_REQUEST_UNITID_O-1 : sv_dma_bus_pack::DMA_REQUEST_TAG_O]] = tr_up_mvb_gen;
                    debug_msg = $sformatf( "\n\t =============== RQ DUT CATCH =============== \n");
                    debug_msg = {debug_msg, $sformatf("\t Transaction NUMBER   : %0d\n",  up_mvb_cnt)};
                    debug_msg = {debug_msg, $sformatf("\t Transaction LENGTH   : %0d\n",  tr_up_mvb_gen.data[sv_dma_bus_pack::DMA_REQUEST_TYPE_O-1 : sv_dma_bus_pack::DMA_REQUEST_LENGTH_O])};
                    debug_msg = {debug_msg, $sformatf("\t Transaction WRITE    : 0x%h\n",  tr_up_mvb_gen.data[sv_dma_bus_pack::DMA_REQUEST_FIRSTIB_O-1 : sv_dma_bus_pack::DMA_REQUEST_TYPE_O])};
                    debug_msg = {debug_msg, $sformatf("\t Transaction PCIE TAG : 0x%h\n",  tr_up_mvb_gen.data[sv_dma_bus_pack::DMA_REQUEST_UNITID_O-1 : sv_dma_bus_pack::DMA_REQUEST_TAG_O])};
                    `uvm_info(this.get_full_name(), debug_msg ,UVM_MEDIUM);
                end
            end
        end
    endtask

endclass


class rc_compare extends uvm_component;
    `uvm_component_utils(uvm_ptc::rc_compare)

    uvm_tlm_analysis_fifo #(pcie_data#(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)) model;

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item#(32))                           dut_mfb;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item#(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)) dut_mvb;

    uvm_logic_vector_array::sequence_item #(32)                           dut_down_mfb_array [logic [8-1 : 0]];
    uvm_logic_vector::sequence_item #(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH) dut_down_mvb_array [logic [8-1 : 0]];

    uvm_ptc_info::sync_tag tag_sync;
    uvm_ptc::up_catch catch_up;
    int unsigned errors;
    int unsigned compared;
    int unsigned down_cnt;
    int unsigned whole_len = 0;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        model = new("model", this);
        dut_mfb   = new("dut_mfb", this);
        dut_mvb   = new("dut_mvb", this);
        errors    = 0;
        compared  = 0;
        down_cnt  = 0;
    endfunction

    task run_phase(uvm_phase phase);
        pcie_data#(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH) tr_model;

        uvm_logic_vector_array::sequence_item#(32)                           tr_dut_mfb;
        uvm_logic_vector::sequence_item#(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH) tr_dut_mvb;

        forever begin
            string msg;
            string debug_msg = "";
            logic[32 : 0] header = '0;

            model.get(tr_model);
            dut_mfb.get(tr_dut_mfb);
            dut_mvb.get(tr_dut_mvb);

            down_cnt++;

            debug_msg = {debug_msg, $sformatf("\n\t Model MFB DOWN TR NUMBER %d: %p\n",  down_cnt, tr_model.data)};
            debug_msg = {debug_msg, $sformatf("\n\t Model MVB DOWN TR NUMBER %d: %h\n",  down_cnt, tr_model.meta)};
            debug_msg = {debug_msg, $sformatf("\n\t DUT MFB DOWN TR NUMBER   %d: %s\n",  down_cnt, tr_dut_mfb.convert2string())};
            debug_msg = {debug_msg, $sformatf("\n\t DUT MVB DOWN TR NUMBER   %d: %s\n",  down_cnt, tr_dut_mvb.convert2string())};
            `uvm_info(this.get_full_name(), debug_msg ,UVM_FULL);

            if (dut_down_mfb_array.exists(tr_dut_mvb.data[20-1 : 12])) begin
                `uvm_fatal(this.get_full_name(), "Transaction exists");
            end else begin
                dut_down_mfb_array[tr_dut_mvb.data[20-1 : 12]] = tr_dut_mfb;
                dut_down_mvb_array[tr_dut_mvb.data[20-1 : 12]] = tr_dut_mvb;
                if (tr_dut_mvb.data[12-1]) begin
                    tag_sync.remove_element(tr_dut_mvb.data[20-1 : 12]);
                end
            end

            if (dut_down_mfb_array.size() != 0) begin
                uvm_logic_vector_array::sequence_item#(32) model_mfb;

                model_mfb = uvm_logic_vector_array::sequence_item#(32)::type_id::create("model_mfb", this);
                model_mfb.data = tr_model.data;
                comp(tr_dut_mvb, tr_dut_mfb, model_mfb);
            end
        end
    endtask

    task comp(uvm_logic_vector::sequence_item#(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH) mvb, uvm_logic_vector_array::sequence_item#(32) dut_mfb, uvm_logic_vector_array::sequence_item#(32) model_mfb);
        string msg;

        msg = {msg, $sformatf("\n\t =============== DOWN COMPARE =============== \n")};
        msg = {msg, $sformatf("\t Transaction NUMBER : %0d\n",  down_cnt)};
        msg = {msg, $sformatf("\t Transaction LENGTH : %0d\n",  mvb.data[10-1 : 0])};
        msg = {msg, $sformatf("\t Transaction TAG    : 0x%h\n",  mvb.data[20-1 : 12])};
        `uvm_info(this.get_full_name(), msg ,UVM_MEDIUM);

        if (catch_up.dut_up_mvb_array.exists(mvb.data[20-1 : 12])) begin

            msg = $sformatf( "\n\t TAG    [dut, model]: 0x%h, 0x%h \n", mvb.data[20-1 : 12], catch_up.dut_up_mvb_array[mvb.data[20-1 : 12]].data[sv_dma_bus_pack::DMA_REQUEST_UNITID_O-1 : sv_dma_bus_pack::DMA_REQUEST_TAG_O]);
            msg = {msg, $sformatf("\t LENGTH [dut, model]: %0d, %0d \n",  mvb.data[10-1 : 0], catch_up.dut_up_mvb_array[mvb.data[20-1 : 12]].data[sv_dma_bus_pack::DMA_REQUEST_LENGTH_W-1 : 0])};
            `uvm_info(this.get_full_name(), msg ,UVM_FULL);

            if (model_mfb.compare(dut_mfb) == 0) begin
                string msg_1;

                msg_1 = $sformatf( "\n\t Transaction number: %d\n\t", down_cnt);
                msg_1 = $sformatf( "\tCheck MFB failed.\n\tModel data %s\n\tDUT data %s\n", model_mfb.convert2string(), dut_mfb.convert2string());
                `uvm_error(this.get_full_name(), msg_1);
                errors++;
            end

            if (mvb.data[10-1 : 0] != dut_mfb.size() || mvb.data[10-1 : 0] != model_mfb.size()) begin
                string msg_1;

                msg_1 = $sformatf( "\n\tTransaction number: %0d\n", down_cnt);
                msg_1 = {msg_1, $sformatf("\t\tCheck of MFB data size and header size failed!\n")};
                msg_1 = {msg_1, $sformatf("\tDUT HDR LENGTH   : %0d\n",  mvb.data[10-1 : 0])};
                msg_1 = {msg_1, $sformatf("\tDUT MFB LENGTH   : %0d\n",  dut_mfb.size())};
                msg_1 = {msg_1, $sformatf("\tMODEL MFB LENGTH : %0d\n",  model_mfb.size())};
                `uvm_error(this.get_full_name(), msg_1);
                errors++;
            end

            if (catch_up.dut_up_mvb_array[mvb.data[20-1 : 12]].data[sv_dma_bus_pack::DMA_REQUEST_UNITID_O-1 : sv_dma_bus_pack::DMA_REQUEST_TAG_O] != mvb.data[20-1 : 12]) begin
                string msg_1;

                msg_1 = $sformatf( "\n\t Transaction number: %d\n\t", down_cnt);
                msg_1 = $sformatf( "\tCheck TAG failed.\n\tModel tag %h\n\tDUT TAG %h\n", catch_up.dut_up_mvb_array[mvb.data[20-1 : 12]].data[sv_dma_bus_pack::DMA_REQUEST_UNITID_O-1 : sv_dma_bus_pack::DMA_REQUEST_TAG_O], mvb.data[20-1 : 12]);
                `uvm_error(this.get_full_name(), msg_1);
                errors++;
            end

            whole_len += mvb.data[10-1 : 0];
            if (mvb.data[12-1]) begin

                if (catch_up.dut_up_mvb_array[mvb.data[20-1 : 12]].data[sv_dma_bus_pack::DMA_REQUEST_LENGTH_W-1 : 0] != whole_len) begin
                    string msg_1;

                    msg_1 = $sformatf( "\n\t Transaction number: %d\n\t", down_cnt);
                    msg_1 = $sformatf( "\tCheck LENGTH failed.\n\tModel LENGTH %d\n\tDUT LENGTH %d\n", catch_up.dut_up_mvb_array[mvb.data[20-1 : 12]].data[sv_dma_bus_pack::DMA_REQUEST_LENGTH_W-1 : 0], mvb.data[10-1 : 0]);
                    `uvm_error(this.get_full_name(), msg_1);
                    errors++;
                end
                compared++;
                whole_len = 0;
            end
        end else begin
            $displayh("UP LIST of MVB %p\n", catch_up.dut_up_mvb_array);
            $write("DOWN MVB TR TAG    : 0x%h\n", mvb.data[20-1 : 12]);
            $write("DOWN MVB TR LENGTH : %0d\n", mvb.data[10-1 : 0]);
            $write("DOWN MVB TR        : 0x%h\n", mvb.data);
            `uvm_error(this.get_full_name(), "Wrong port or read request was not send");
        end

        if (mvb.data[12-1]) begin
            catch_up.dut_up_mfb_array.delete(mvb.data[20-1 : 12]);
            catch_up.dut_up_mvb_array.delete(mvb.data[20-1 : 12]);
        end
        dut_down_mvb_array.delete(mvb.data[20-1 : 12]);
        dut_down_mfb_array.delete(mvb.data[20-1 : 12]);
    endtask

endclass


class compare #(PCIE_UPHDR_WIDTH, PCIE_PREFIX_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_ptc::compare #(PCIE_UPHDR_WIDTH, PCIE_PREFIX_WIDTH))

    int unsigned errors;
    int unsigned compared;

    pcie_data#(PCIE_UPHDR_WIDTH)                        tr_table[$];

    uvm_logic_vector_array::sequence_item #(32)         rq_mfb_tr_table[$];
    uvm_logic_vector::sequence_item #(PCIE_UPHDR_WIDTH) rq_mvb_tr_table[$];
    uvm_logic_vector::sequence_item #(PCIE_UPHDR_WIDTH) rq_prefix_mvb_tr_table[$];

    function new(string name, uvm_component parent);
        super.new(name, parent);
        errors     = 0;
        compared   = 0;
    endfunction

    task comp();
        pcie_data#(PCIE_UPHDR_WIDTH) tr_model;
        uvm_logic_vector_array::sequence_item #(32)         tr_model_up_mfb;
        uvm_logic_vector::sequence_item #(PCIE_UPHDR_WIDTH) tr_model_up_mvb;

        uvm_logic_vector_array::sequence_item #(32)          tr_dut_rq_mfb;
        uvm_logic_vector::sequence_item #(PCIE_UPHDR_WIDTH)  tr_dut_rq_mvb;
        uvm_logic_vector::sequence_item #(PCIE_PREFIX_WIDTH) tr_dut_rq_mvb_pref;
        string debug_msg = "";

        if (tr_table.size() != 0 && rq_mvb_tr_table.size() != 0) begin

            tr_dut_rq_mvb = rq_mvb_tr_table.pop_front();
            tr_dut_rq_mfb = rq_mfb_tr_table.pop_front();
            tr_model = tr_table.pop_front();
            tr_model_up_mfb = uvm_logic_vector_array::sequence_item #(32)::type_id::create();
            tr_model_up_mfb.data = tr_model.data;
            tr_model_up_mvb = uvm_logic_vector::sequence_item #(PCIE_UPHDR_WIDTH)::type_id::create();
            tr_model_up_mvb.data = tr_model.meta;

            debug_msg = {debug_msg, $sformatf("\n\t Model RQ DATA TR:   %s\n",  tr_model_up_mfb.convert2string())};
            debug_msg = {debug_msg, $sformatf("\n\t Model RQ HEADER TR: %s\n",  tr_model_up_mvb.convert2string())};
            debug_msg = {debug_msg, $sformatf("\n\t DUT RQ DATA TR:     %s\n",  tr_dut_rq_mfb.convert2string())};
            debug_msg = {debug_msg, $sformatf("\n\t DUT RQ HEADER TR:   %s\n",  tr_dut_rq_mvb.convert2string())};
            `uvm_info(this.get_full_name(), debug_msg ,UVM_DEBUG);

            compared++;
            if (tr_dut_rq_mfb.compare(tr_model_up_mfb) == 0 || tr_dut_rq_mvb.compare(tr_model_up_mvb) == 0) begin
                string msg;

                errors++;
                msg = $sformatf("\n\tCheck MVB or MFB packet failed.\n\tModel MFB %s\n\tDUT MFB %s\n\n\tModel MVB\n%s\n\tDUT MVB\n%s\n COMPARED %d\n", tr_model_up_mfb.convert2string(),
                tr_dut_rq_mfb.convert2string(), tr_model_up_mvb.convert2string(), tr_dut_rq_mvb.convert2string(), compared);
                `uvm_error(this.get_full_name(), msg);
            end
        end
    endtask
endclass



class scoreboard #(META_WIDTH, MFB_DOWN_REGIONS, MFB_UP_REGIONS, DMA_MVB_UP_ITEMS, PCIE_PREFIX_WIDTH, PCIE_UPHDR_WIDTH, RQ_TUSER_WIDTH, DMA_MVB_DOWN_ITEMS, PCIE_DOWNHDR_WIDTH, DMA_PORTS, ENDPOINT_TYPE, DEVICE) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_ptc::scoreboard #(META_WIDTH, MFB_DOWN_REGIONS, MFB_UP_REGIONS, DMA_MVB_UP_ITEMS, PCIE_PREFIX_WIDTH, PCIE_UPHDR_WIDTH, RQ_TUSER_WIDTH, DMA_MVB_DOWN_ITEMS, PCIE_DOWNHDR_WIDTH, DMA_PORTS, ENDPOINT_TYPE, DEVICE))

    localparam PORTS_W_FIX = (DMA_PORTS > 1) ? $clog2(DMA_PORTS) : 1;
    localparam HDR_USER_WIDTH = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? PCIE_UPHDR_WIDTH : PCIE_UPHDR_WIDTH+RQ_TUSER_WIDTH;

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(32))           rc_mfb_in;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(PCIE_DOWNHDR_WIDTH)) rc_meta_in;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(PCIE_PREFIX_WIDTH))  rc_prefix_mvb_in;

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(32))           rq_mfb_out;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(PCIE_UPHDR_WIDTH))   rq_mvb_out;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(PCIE_PREFIX_WIDTH))  rq_prefix_mvb_out;
    uvm_analysis_port   #(uvm_logic_vector::sequence_item #(HDR_USER_WIDTH))     rq_hdr_user_out;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(RQ_TUSER_WIDTH))     rq_axi_meta_out;

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(32))                         up_mfb_in[DMA_PORTS];
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(sv_dma_bus_pack::DMA_UPHDR_WIDTH)) up_mvb_in[DMA_PORTS];

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item #(32))                           down_mfb_out[DMA_PORTS];
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)) down_mvb_out[DMA_PORTS];

    // Model FIFO
    uvm_tlm_analysis_fifo#(pcie_data#(PCIE_UPHDR_WIDTH)) model_up;
    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(32))                           model_down_mfb_out[DMA_PORTS];
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH)) model_down_mvb_out[DMA_PORTS];

    // DUT FIFO
    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(32))                            dut_down_mfb_out[DMA_PORTS];
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH))  dut_down_mvb_out[DMA_PORTS];

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(32))           dut_rq_mfb_out;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(PCIE_UPHDR_WIDTH))   dut_rq_mvb_out;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(PCIE_PREFIX_WIDTH))  dut_rq_prefix_mvb_out;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(RQ_TUSER_WIDTH))     dut_rq_axi_meta_out;

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(32))           dut_rc_mfb_out;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(PCIE_DOWNHDR_WIDTH)) dut_rc_meta_out;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(PCIE_PREFIX_WIDTH))  dut_rc_prefix_mvb_out;

    //uvm_ptc_info::sync_tag tag_sync[DMA_PORTS];
    model_rc #(DMA_PORTS, PCIE_UPHDR_WIDTH) m_model;
    down_model #(DMA_PORTS) m_down_model;
    uvm_ptc::compare #(PCIE_UPHDR_WIDTH, PCIE_PREFIX_WIDTH) out_compare[DMA_PORTS];
    uvm_ptc::rc_compare answer_compare[DMA_PORTS];
    uvm_ptc::up_catch catch_up[DMA_PORTS];
    int unsigned errors;
    int unsigned compared;
    int unsigned rq_read_cnt[DMA_PORTS];
    int unsigned rq_write_cnt[DMA_PORTS];

    // Contructor of scoreboard.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        rc_mfb_in             = new("rc_mfb_in",             this);
        rc_meta_in            = new("rc_meta_in",            this);
        rc_prefix_mvb_in      = new("rc_prefix_mvb_in",      this);

        dut_rc_mfb_out        = new("dut_rc_mfb_out",        this);
        dut_rc_meta_out       = new("dut_rc_meta_out",       this);
        dut_rc_prefix_mvb_out = new("dut_rc_prefix_mvb_out", this);

        rq_mfb_out            = new("rq_mfb_out",            this);
        rq_axi_meta_out       = new("rq_axi_meta_out",       this);
        rq_mvb_out            = new("rq_mvb_out",            this);
        rq_prefix_mvb_out     = new("rq_prefix_mvb_out",     this);
        rq_hdr_user_out       = new("rq_hdr_user_out",       this);

        dut_rq_mfb_out        = new("dut_rq_mfb_out",        this);
        dut_rq_axi_meta_out   = new("dut_rq_axi_meta_out",   this);
        dut_rq_mvb_out        = new("dut_rq_mvb_out",        this);
        dut_rq_prefix_mvb_out = new("dut_rq_prefix_mvb_out", this);

        model_up = new("model_up", this);

        for (int unsigned it = 0; it < DMA_PORTS; it++) begin
            string it_str;
            it_str.itoa(it);
            up_mfb_in[it]          = new({"up_mfb_in_",          it_str}, this);
            up_mvb_in[it]          = new({"up_mvb_in_",          it_str}, this);
            down_mvb_out[it]       = new({"down_mvb_out_",       it_str}, this);
            down_mfb_out[it]       = new({"down_mfb_out_",       it_str}, this);
            dut_down_mfb_out[it]   = new({"dut_down_mfb_out_",   it_str}, this);
            dut_down_mvb_out[it]   = new({"dut_down_mvb_out_",   it_str}, this);
            model_down_mfb_out[it] = new({"model_down_mfb_out_", it_str}, this);
            model_down_mvb_out[it] = new({"model_down_mvb_out_", it_str}, this);

            rq_read_cnt[it]  = '0;
            rq_write_cnt[it] = '0;
        end
        errors = 0;
        compared = 0;
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (dut_rq_mfb_out.used()      != 0);
        ret |= (dut_rq_mvb_out.used()      != 0);
        ret |= (dut_rc_mfb_out.used()      != 0);
        ret |= (dut_rc_meta_out.used()     != 0);
        ret |= (model_up.used() != 0);
        ret |= (dut_rq_axi_meta_out.used() != 0);

        for (int it = 0; it < DMA_PORTS; it++) begin
            ret |= (model_down_mfb_out[it].used() != 0);
            ret |= (model_down_mvb_out[it].used() != 0);
        end
        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        if (DEVICE == "STRATIX10" || DEVICE ==  "AGILEX") begin
            m_model = model_rc_intel #(DMA_PORTS, PCIE_UPHDR_WIDTH, ENDPOINT_TYPE)::type_id::create("m_model", this);
        end else if (DEVICE == "7SERIES" || DEVICE == "VIRTEX6" || DEVICE == "ULTRASCALE") begin
            m_model = model_rc_xilinx #(DMA_PORTS, PCIE_UPHDR_WIDTH)::type_id::create("m_model", this);
        end

        m_down_model = down_model #(DMA_PORTS)::type_id::create("m_down_model", this);
        if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin
            m_down_model.model_rc = model_down_input_fifo_intel#(PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH, DMA_PORTS)::type_id::create("model_rc", m_down_model);
        end else if (DEVICE == "7SERIES" || DEVICE == "VIRTEX6" || DEVICE == "ULTRASCALE") begin
            m_down_model.model_rc = model_down_input_fifo_xilinx#(PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH, DMA_PORTS)::type_id::create("model_rc", m_down_model);
        end else begin
            `uvm_fatal(this.get_full_name(), $sformatf("\n\tUnknow device %s", DEVICE));
        end


        for (int it = 0; it < DMA_PORTS; it++) begin
            string it_string;

            it_string.itoa(it);
            m_model.model_up[it] = model_rc_input_fifo#(sv_dma_bus_pack::DMA_UPHDR_WIDTH)::type_id::create({"model_up_", it_string}, this);


            out_compare[it]    = uvm_ptc::compare #(PCIE_UPHDR_WIDTH, PCIE_PREFIX_WIDTH)::type_id::create({"out_compare_", it_string}, this);
            answer_compare[it] = uvm_ptc::rc_compare::type_id::create({"answer_compare_", it_string}, this);
            catch_up[it]       = uvm_ptc::up_catch::type_id::create({"catch_up_", it_string}, this);
        end

    endfunction

    function int unsigned error_cnt();
        int unsigned ret = 0;
        ret |= (out_compare[0].errors != 0);
        ret |= (answer_compare[0].errors != 0);
        return ret;
    endfunction

    function void connect_phase(uvm_phase phase);
        model_down_input_fifo#(PCIE_DOWNHDR_WIDTH, PCIE_PREFIX_WIDTH) down_model_fifo;

        // Model inputs
        $cast(down_model_fifo, m_down_model.model_rc);
        rc_mfb_in.connect(down_model_fifo.mfb_in.analysis_export);
        rc_meta_in.connect(down_model_fifo.meta_in.analysis_export);
        rc_prefix_mvb_in.connect(down_model_fifo.prefix_in.analysis_export);

        // DUT outputs
        rq_mfb_out.connect(dut_rq_mfb_out.analysis_export);
        rq_axi_meta_out.connect(dut_rq_axi_meta_out.analysis_export);
        rq_mvb_out.connect(dut_rq_mvb_out.analysis_export);
        rq_prefix_mvb_out.connect(dut_rq_prefix_mvb_out.analysis_export);

        // Model outputs
        for (int it = 0; it < DMA_PORTS; it++) begin
            model_rc_input_fifo#(sv_dma_bus_pack::DMA_UPHDR_WIDTH) fifo_model_up;
            // Model inputs
            $cast(fifo_model_up, m_model.model_up[it]);
            up_mfb_in[it].connect(fifo_model_up.mfb.analysis_export);
            up_mvb_in[it].connect(fifo_model_up.mvb.analysis_export);

            // Model outputs
            m_down_model.model_down[it].connect(answer_compare[it].model.analysis_export);
            down_mfb_out[it].connect(answer_compare[it].dut_mfb.analysis_export);
            down_mvb_out[it].connect(answer_compare[it].dut_mvb.analysis_export);

            up_mfb_in[it].connect(catch_up[it].up_mfb_gen.analysis_export);
            up_mvb_in[it].connect(catch_up[it].up_mvb_gen.analysis_export);
            answer_compare[it].catch_up = catch_up[it];

        end

        m_model.model_down.connect(model_up.analysis_export);
    endfunction

    task run_phase(uvm_phase phase);
        pcie_data#(PCIE_UPHDR_WIDTH)  tr_model_up;

        uvm_logic_vector_array::sequence_item #(32)          tr_dut_rq_mfb;
        uvm_logic_vector::sequence_item #(PCIE_UPHDR_WIDTH)  tr_dut_rq_mvb;
        uvm_logic_vector::sequence_item #(HDR_USER_WIDTH)    tr_dut_rq_mvb_user;
        uvm_logic_vector::sequence_item #(RQ_TUSER_WIDTH)    tr_dut_rq_axi_meta;

        uvm_logic_vector_array::sequence_item #(32)                           tr_dut_down_mfb[DMA_PORTS];
        uvm_logic_vector::sequence_item #(sv_dma_bus_pack::DMA_DOWNHDR_WIDTH) tr_dut_down_mvb[DMA_PORTS];

        int unsigned port_model = 0;
        int unsigned port_dut   = 0;
        logic type_n_model      = '0;
        logic type_n_dut        = '0;
        int total_cnt = 0;

        forever begin
            string debug_msg = "";
            logic [7 : 0] tag_model = 0;
            logic [7 : 0] tag_dut = 0;
            int len_model = 0;
            int len_dut = 0;
            tr_dut_rq_mvb_user = uvm_logic_vector::sequence_item #(HDR_USER_WIDTH)::type_id::create("tr_dut_rq_mvb_user");

            model_up.get(tr_model_up);
            dut_rq_mfb_out.get(tr_dut_rq_mfb);
            dut_rq_mvb_out.get(tr_dut_rq_mvb);
            if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin
                tr_dut_rq_mvb_user.copy(tr_dut_rq_mvb);
            end else begin
                dut_rq_axi_meta_out.get(tr_dut_rq_axi_meta);
                tr_dut_rq_mvb_user.data = {tr_dut_rq_axi_meta.data, tr_dut_rq_mvb.data};
            end
            rq_hdr_user_out.write(tr_dut_rq_mvb_user);

            total_cnt++;

            debug_msg = $sformatf( "\n\t =============== RQ SCOREBOARD DATA =============== \n");
            debug_msg = {debug_msg, $sformatf("\t Model AXI RQ TR: %p\n",  tr_model_up.data)};
            debug_msg = {debug_msg, $sformatf("\t Model RQ HEADER TR: %h\n",  tr_model_up.meta)};
            debug_msg = {debug_msg, $sformatf("\t DUT AXI RQ TR: %s\n",  tr_dut_rq_mfb.convert2string())};
            debug_msg = {debug_msg, $sformatf("\t DUT RQ HEADER TR: %s\n",  tr_dut_rq_mvb.convert2string())};
            `uvm_info(this.get_full_name(), debug_msg ,UVM_MEDIUM);

            if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin
                if (DMA_PORTS > 1) begin
                    port_model = int'(tr_model_up.meta[48+PORTS_W_FIX-1 : 48]);
                    port_dut   = int'(tr_dut_rq_mvb.data[48+PORTS_W_FIX-1 : 48]);
                end else begin
                    port_model = 0;
                    port_dut   = 0;
                end

                type_n_model = tr_model_up.meta[30];
                type_n_dut = tr_dut_rq_mvb.data[30];
                tag_model = (tr_model_up.meta[48-1 : 40]);
                tag_dut = (tr_dut_rq_mvb.data[48-1 : 40]);
                len_model = int'(tr_model_up.meta[10-1 : 0]);
                len_dut = int'(tr_dut_rq_mvb.data[10-1 : 0]);
            end else begin
                if (DMA_PORTS > 1) begin
                    port_model = int'(tr_model_up.meta[80+PORTS_W_FIX-1 : 80]);
                    port_dut   = int'(tr_dut_rq_mvb.data[80+PORTS_W_FIX-1 : 80]);
                end else begin
                    port_model = 0;
                    port_dut   = 0;
                end

                type_n_model = tr_model_up.meta[75];
                type_n_dut = tr_dut_rq_mvb.data[75];
                tag_model = (tr_model_up.meta[103 : 96]);
                tag_dut = (tr_dut_rq_mvb.data[103 : 96]);
                len_model = int'(tr_model_up.meta[75-1 : 64]);
                len_dut = int'(tr_dut_rq_mvb.data[75-1 : 64]);
            end

            debug_msg = $sformatf( "\n\t =============== RQ SCOREBOARD INFO - PORT %0d =============== \n", port_dut);
            debug_msg = {debug_msg, $sformatf("\t DUT TR NUMBER : %0d\n",  total_cnt)};
            debug_msg = {debug_msg, $sformatf("\t DUT TR LENGTH : %0d\n",  len_dut)};
            debug_msg = {debug_msg, $sformatf("\t DUT TR WRITE  : 0x%h\n",  type_n_dut)};
            debug_msg = {debug_msg, $sformatf("\t DUT TR TAG    : 0x%h\n",  tag_dut)};
            `uvm_info(this.get_full_name(), debug_msg ,UVM_MEDIUM);

            if (type_n_model == 1'b1) begin
                out_compare[port_model].tr_table.push_back(tr_model_up);
            end
            if (type_n_dut == 1'b1) begin
                out_compare[port_dut].rq_mfb_tr_table.push_back(tr_dut_rq_mfb);
                out_compare[port_dut].rq_mvb_tr_table.push_back(tr_dut_rq_mvb);
                rq_write_cnt[port_dut]++;
            end else begin
                rq_read_cnt[port_dut]++;
            end

            for (int i = 0; i < DMA_PORTS; i++) begin
                out_compare[i].comp();
            end
        end
    endtask

    // TODO
    function void report_phase(uvm_phase phase);
       int unsigned errors = 0;
       string msg = "";

       for (int unsigned it = 0; it < DMA_PORTS; it++) begin
            msg = {msg, $sformatf("\n\t OUT OUTPUT [%0d] compared %0d errors %0d",  it, out_compare[it].compared, out_compare[it].errors)};
            msg = {msg, $sformatf("\n\t ANSWER OUTPUT [%0d] compared %0d errors %0d",  it, answer_compare[it].compared, answer_compare[it].errors)};
            msg = {msg, $sformatf("\n\t RQ TR TABLE [%0d] size %0d UP TR TABLE [%0d] size %0d\n",  it, out_compare[it].rq_mvb_tr_table.size(), it,  out_compare[it].tr_table.size())};
            msg = {msg, $sformatf("\n\t model_down_mfb_out[%0d] USED [%0d]",  it, model_down_mfb_out[it].used())};
            msg = {msg, $sformatf("\n\t model_down_mvb_out[%0d] USED [%0d]\n",  it, model_down_mvb_out[it].used())};
       end
            msg = {msg, $sformatf("\n\t dut_rq_mfb_out USED [%0d]",  dut_rq_mfb_out.used())};
            msg = {msg, $sformatf("\n\t dut_rq_mvb_out USED [%0d]",  dut_rq_mvb_out.used())};
            msg = {msg, $sformatf("\n\t dut_rc_mfb_out USED [%0d]",  dut_rc_mfb_out.used())};
            msg = {msg, $sformatf("\n\t dut_rc_meta_out USED [%0d]",  dut_rc_meta_out.used())};
            msg = {msg, $sformatf("\n\t model_up USED [%0d]",  model_up.used())};
            msg = {msg, $sformatf("\n\t dut_rq_axi_meta_out USED [%0d]\n",  dut_rq_axi_meta_out.used())};
            msg = {msg, $sformatf("\n\t Final USED [%0d]",  this.used())};

       if (this.error_cnt() == 0 && this.used() == 0) begin
           `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
       end else begin
           `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------"}, UVM_NONE)
       end
    endfunction

endclass
