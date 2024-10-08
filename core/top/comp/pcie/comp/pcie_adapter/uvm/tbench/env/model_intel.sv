//-- model_intel.sv: Model of implementation
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

class model_intel #(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W, ENDPOINT_TYPE)
extends model_base #(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W);

    `uvm_component_param_utils(uvm_pcie_adapter::model_intel#(CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W, ENDPOINT_TYPE))

    // Model inputs
    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(CQ_MFB_ITEM_WIDTH)) avst_down_data_in;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(AVST_DOWN_META_W))        avst_down_meta_in;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(CC_MFB_META_W))           mfb_cc_meta_in;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(RQ_MFB_META_W))           mfb_rq_meta_in;

    uvm_analysis_port #(uvm_logic_vector_array::sequence_item #(CC_MFB_ITEM_WIDTH)) avst_up_data_out;
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(AVST_UP_META_W))          avst_up_meta_out;
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(RC_MFB_META_W))           mfb_rc_meta_out;
    uvm_analysis_port #(uvm_logic_vector::sequence_item #(CQ_MFB_META_W))           mfb_cq_meta_out;

    logic rws[$];
    int rq_cnt = 0;
    int cc_cnt = 0;

    function new(string name = "model_intel", uvm_component parent = null);
        super.new(name, parent);

        avst_down_data_in = new("avst_down_data_in", this);
        avst_down_meta_in = new("avst_down_meta_in", this);
        mfb_cc_meta_in    = new("mfb_cc_meta_in", this);
        mfb_rq_meta_in    = new("mfb_rq_meta_in", this);

        avst_up_data_out  = new("avst_up_data_out" , this);
        avst_up_meta_out  = new("avst_up_meta_out" , this);
        mfb_rc_meta_out   = new("mfb_rc_meta_out" , this);
        mfb_cq_meta_out   = new("mfb_cq_meta_out" , this);

    endfunction

    function logic solve_type(logic [8-1 : 0] tlp_type);
        logic ret;

        case (tlp_type)
            8'b00001010 :
            begin
                ret  = 1'b1;
            end
            8'b01001010 :
            begin
                ret  = 1'b1;
            end
            8'b00001011 :
            begin
                ret  = 1'b1;
            end
            8'b01001011 :
            begin
                ret  = 1'b1;
            end
            default : ret = 1'b0;
        endcase

        return ret;
    endfunction

    task run_down_meta();
        uvm_logic_vector::sequence_item #(AVST_DOWN_META_W) tr_avst_down_meta_in;

        uvm_logic_vector::sequence_item #(RC_MFB_META_W) tr_mfb_rc_meta_out;
        uvm_logic_vector::sequence_item #(CQ_MFB_META_W) tr_mfb_cq_meta_out;

        logic [8-1 : 0] tlp_type;
        logic rw;
        string msg = "\n";

        forever begin

            $swrite(msg, "%s--------------------------\n", msg);
            $swrite(msg, "%s\tDOWN META MODEL\n", msg);
            $swrite(msg, "%s--------------------------\n", msg);

            avst_down_meta_in.get(tr_avst_down_meta_in);
            $swrite(msg, "%s\tAVST DOWN INPUT META %s\n", msg, tr_avst_down_meta_in.convert2string());
            tlp_type = tr_avst_down_meta_in.data[128-1 : 120];

            rw = solve_type(tlp_type);
            rws.push_back(rw);

            if (rw == 1'b0) begin 
                tr_mfb_cq_meta_out      = uvm_logic_vector::sequence_item #(CQ_MFB_META_W)::type_id::create("tr_mfb_cq_meta_out", this);
                tr_mfb_cq_meta_out.data = '0;
                tr_mfb_cq_meta_out.data = {tr_avst_down_meta_in.data[163-1 : 160], tr_avst_down_meta_in.data[160-1 : 128], tr_avst_down_meta_in.data[32-1 : 0], tr_avst_down_meta_in.data[64-1 : 32], tr_avst_down_meta_in.data[96-1 : 64], tr_avst_down_meta_in.data[128-1 : 96]};

                $swrite(msg, "%s\tMFB CQ OUTPUT META %s Time %t\n", msg, tr_mfb_cq_meta_out.convert2string(), $time());

                mfb_cq_meta_out.write(tr_mfb_cq_meta_out);
            end
            else begin
                tr_mfb_rc_meta_out      = uvm_logic_vector::sequence_item #(RC_MFB_META_W)::type_id::create("tr_mfb_rc_meta_out", this);
                tr_mfb_rc_meta_out.data = {tr_avst_down_meta_in.data[32-1 : 0], tr_avst_down_meta_in.data[64-1 : 32], tr_avst_down_meta_in.data[96-1 : 64], tr_avst_down_meta_in.data[128-1 : 96]};

                $swrite(msg, "%s\tMFB RC OUTPUT META %s Time %t\n", msg, tr_mfb_rc_meta_out.convert2string(), $time());

                mfb_rc_meta_out.write(tr_mfb_rc_meta_out);
            end

            `uvm_info(get_type_name(), msg, UVM_FULL)

        end

    endtask

    // (RC+CQ) Interface
    task run_down_data();
        uvm_logic_vector::sequence_item #(AVST_DOWN_META_W)        tr_avst_down_meta_in;
        uvm_logic_vector_array::sequence_item #(CQ_MFB_ITEM_WIDTH) tr_avst_down_data_in;

        uvm_logic_vector::sequence_item #(RC_MFB_META_W) tr_mfb_rc_meta_out;
        uvm_logic_vector::sequence_item #(CQ_MFB_META_W) tr_mfb_cq_meta_out;

        logic [8-1 : 0] tlp_type;
        logic rw;
        string msg = "\n";

        forever begin

            $swrite(msg, "%s--------------------------\n", msg);
            $swrite(msg, "%s\tDOWN DATA MODEL\n", msg);
            $swrite(msg, "%s--------------------------\n", msg);

            avst_down_data_in.get(tr_avst_down_data_in);
            $swrite(msg, "%s\tAVST DOWN INPUT DATA %s\n", msg, tr_avst_down_data_in.convert2string());
            `uvm_info(get_type_name(), msg, UVM_FULL)

            rw = rws.pop_front();

            if (rw == 1'b0) begin
                mfb_cq_data_out.write(tr_avst_down_data_in);
            end
            else begin
                mfb_rc_data_out.write(tr_avst_down_data_in);
            end
        end
    endtask

    task run_cc_meta();
        uvm_logic_vector::sequence_item #(CC_MFB_META_W)  tr_mfb_cc_meta_in;
        uvm_logic_vector::sequence_item #(AVST_UP_META_W) tr_avst_up_meta_out;

        string msg = "\n";

        forever begin

            $swrite(msg, "%s--------------------------\n", msg);
            $swrite(msg, "%s\tCC META MODEL\n", msg);
            $swrite(msg, "%s--------------------------\n", msg);

            mfb_cc_meta_in.get(tr_mfb_cc_meta_in);

            tr_avst_up_meta_out      = uvm_logic_vector::sequence_item #(AVST_UP_META_W)::type_id::create("tr_avst_up_meta_out", this);

            tr_avst_up_meta_out.data = {32'bx, tr_mfb_cc_meta_in.data[32-1 : 0], tr_mfb_cc_meta_in.data[64-1 : 32], tr_mfb_cc_meta_in.data[96-1 : 64], tr_mfb_cc_meta_in.data[128-1 : 96]};

            $swrite(msg, "%s\tMFB CC INPUT META %s Time %t\n", msg, tr_mfb_cc_meta_in.convert2string(), $time());
            $swrite(msg, "%s\tMFB CC OUTPUT META %s Time %t\n", msg, tr_avst_up_meta_out.convert2string(), $time());
            avst_up_meta_out.write(tr_avst_up_meta_out);
            `uvm_info(get_type_name(), msg, UVM_FULL)
        end
    endtask

    task run_rq_meta();
        uvm_logic_vector::sequence_item #(RQ_MFB_META_W)  tr_mfb_rq_meta_in;
        uvm_logic_vector::sequence_item #(AVST_UP_META_W) tr_avst_up_meta_out;

        string msg = "\n";

        forever begin

            $swrite(msg, "%s--------------------------\n", msg);
            $swrite(msg, "%s\tRQ META MODEL\n", msg);
            $swrite(msg, "%s--------------------------\n", msg);

            mfb_rq_meta_in.get(tr_mfb_rq_meta_in);

            tr_avst_up_meta_out      = uvm_logic_vector::sequence_item #(AVST_UP_META_W)::type_id::create("tr_avst_up_meta_out", this);
            tr_avst_up_meta_out.data = '0;
            tr_avst_up_meta_out.data = {1'b0, tr_mfb_rq_meta_in.data[AVST_UP_META_W-2 : 128], tr_mfb_rq_meta_in.data[32-1 : 0], tr_mfb_rq_meta_in.data[64-1 : 32], tr_mfb_rq_meta_in.data[96-1 : 64], tr_mfb_rq_meta_in.data[128-1 : 96]};

            $swrite(msg, "%s\tMFB RQ INPUT META %s Time %t\n", msg, tr_mfb_rq_meta_in.convert2string(), $time());
            $swrite(msg, "%s\tMFB RQ OUTPUT META %s Time %t\n", msg, tr_avst_up_meta_out.convert2string(), $time());
            avst_up_meta_out.write(tr_avst_up_meta_out);
            `uvm_info(get_type_name(), msg, UVM_FULL)
        end
    endtask

    // (CC+RQ) Interface
    task run_up_cc();
        uvm_logic_vector_array::sequence_item #(CC_MFB_ITEM_WIDTH) tr_mfb_cc_data_in;
        uvm_logic_vector::sequence_item #(CC_MFB_META_W)  tr_mfb_cc_meta_in;
        uvm_logic_vector::sequence_item #(AVST_UP_META_W) tr_avst_up_meta_out;

        string msg = "\n";

        forever begin

            $swrite(msg, "%s--------------------------\n", msg);
            $swrite(msg, "%s\tAVST UP CC MODEL\n", msg);
            $swrite(msg, "%s--------------------------\n", msg);

            mfb_cc_data_in.get(tr_mfb_cc_data_in);
            avst_up_data_out.write(tr_mfb_cc_data_in);
            `uvm_info(get_type_name(), msg, UVM_FULL)
        end
    endtask

    task run_up_rq();
        uvm_logic_vector_array::sequence_item #(RQ_MFB_ITEM_WIDTH) tr_mfb_rq_data_in;
        uvm_logic_vector::sequence_item #(RQ_MFB_META_W)  tr_mfb_rq_meta_in;
        uvm_logic_vector::sequence_item #(AVST_UP_META_W) tr_avst_up_meta_out;

        string msg = "\n";

        forever begin

            $swrite(msg, "%s--------------------------\n", msg);
            $swrite(msg, "%s\tAVST UP RQ MODEL\n", msg);
            $swrite(msg, "%s--------------------------\n", msg);

            mfb_rq_data_in.get(tr_mfb_rq_data_in);
            $swrite(msg, "%s\tMFB RQ DATA %s Time %t\n", msg, tr_mfb_rq_data_in.convert2string(), $time());
            `uvm_info(get_type_name(), msg, UVM_FULL)

            avst_up_data_out.write(tr_mfb_rq_data_in);
        end
    endtask

    task run_phase(uvm_phase phase);
        fork
            // Ask what is correct (Sond in design or this way?)
            run_cc_meta();
            run_rq_meta();
            run_down_data();
            run_down_meta();
            run_up_cc();
            run_up_rq();
        join_none
    endtask

endclass
