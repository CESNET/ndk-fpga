// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kondys <xkondy00@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`uvm_analysis_imp_decl(_data)
`uvm_analysis_imp_decl(_meta)

class model_input_fifo#(ITEM_WIDTH, META_WIDTH) extends uvm_component;
    `uvm_component_param_utils(net_mod_logic_env::model_input_fifo#(ITEM_WIDTH, META_WIDTH))

    typedef model_input_fifo#(ITEM_WIDTH, META_WIDTH) this_type;
    uvm_analysis_imp_data#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH), this_type) analysis_export_data;
    uvm_analysis_imp_meta#(uvm_logic_vector::sequence_item#(META_WIDTH),       this_type) analysis_export_meta;

    uvm_analysis_port#(model_data#(ITEM_WIDTH, META_WIDTH))  port;

    typedef struct {
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) input_item;
        time  input_time;
    } data_item;

    typedef struct {
        uvm_logic_vector::sequence_item#(META_WIDTH) input_item;
        time  input_time;
    } meta_item;

    protected data_item tmp_data[$];
    protected meta_item tmp_meta[$];
    protected uvm_component parent;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        analysis_export_data = new("analysis_export_data", this); 
        analysis_export_meta = new("analysis_export_meta", this);
        port                 = new("port", this);
    endfunction

    function void write_data(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) t);
        tmp_data.push_back('{t, $time()});
    endfunction

    function void write_meta(uvm_logic_vector::sequence_item#(META_WIDTH) t);
        tmp_meta.push_back('{t, $time()});
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (tmp_data.size() != 0);
        ret |= (tmp_meta.size() != 0);
        return ret;
    endfunction

    task run_phase(uvm_phase phase);
        model_data#(ITEM_WIDTH, META_WIDTH) item;

        forever begin
            data_item data;
            meta_item meta;

            wait (tmp_meta.size() != 0 && tmp_data.size() != 0);
            data = tmp_data.pop_front();
            meta = tmp_meta.pop_front();

            item = model_data#(ITEM_WIDTH, META_WIDTH)::type_id::create("item", this);
            item.data = data.input_item;
            item.meta = meta.input_item;
            item.tag  = "USER_TO_CORE";
            item.start[{item.tag, " DATA"}] = data.input_time;
            item.start[{item.tag, " META"}] = meta.input_time;

            port.write(item);
        end
    endtask
endclass

class comparer_meta #(ITEM_WIDTH, META_WIDTH) extends uvm_common::comparer_base_tagged#(model_data#(ITEM_WIDTH, META_WIDTH), uvm_logic_vector::sequence_item#(META_WIDTH));
    `uvm_component_param_utils(net_mod_logic_env::comparer_meta#(ITEM_WIDTH, META_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        //return tr_model.meta.compare(tr_dut);
        return (tr_dut.data[24-1:0] == tr_model.meta.data[24-1:0]);
    endfunction
endclass

class comparer_data #(ITEM_WIDTH, META_WIDTH) extends uvm_common::comparer_base_tagged#(model_data#(ITEM_WIDTH, META_WIDTH), uvm_logic_vector_array::sequence_item#(ITEM_WIDTH));
    `uvm_component_param_utils(net_mod_logic_env::comparer_data#(ITEM_WIDTH, META_WIDTH))

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        return tr_model.data.compare(tr_dut);
    endfunction
endclass


class scoreboard #(CHANNELS, REGIONS, ITEM_WIDTH, META_WIDTH, HDR_WIDTH, RX_MAC_LITE_REGIONS) extends uvm_scoreboard;
    `uvm_component_param_utils(net_mod_logic_env::scoreboard #(CHANNELS, REGIONS, ITEM_WIDTH, META_WIDTH, HDR_WIDTH, RX_MAC_LITE_REGIONS))

    // TX path
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))         tx_input_data;
    uvm_analysis_export #(uvm_logic_vector::sequence_item #(META_WIDTH))              tx_input_meta;
    protected model_input_fifo#(ITEM_WIDTH, META_WIDTH)                               tx_input; 

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))         tx_out[CHANNELS];
    //comparesrs
    protected uvm_common::comparer_ordered#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) tx_compare[CHANNELS];

    // RX path
    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))        rx_input_data[CHANNELS]; // data for model

    uvm_analysis_export #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))        rx_out_data; // MFB data from DUT
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(HDR_WIDTH))               rx_out_hdr; // MVB headers used to identify channel

    //comparers
    // Thing about comparer. Comparing have to be same as because output have to be tagged same.
    protected comparer_data #(ITEM_WIDTH, HDR_WIDTH) rx_compare_data;
    protected comparer_meta #(ITEM_WIDTH, HDR_WIDTH) rx_compare_meta;

    // MVB discard
    uvm_analysis_export #(uvm_logic_vector::sequence_item#(1)) mvb_discard[CHANNELS];
    protected model #(CHANNELS, ITEM_WIDTH, META_WIDTH, HDR_WIDTH) m_model;

    function new(string name, uvm_component parent);
        super.new(name, parent);

        // TX path
        tx_input_data = new("tx_input_data", this);
        tx_input_meta = new("tx_input_meta", this);

        // RX path
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            string it_str;
            it_str.itoa(it);

            tx_out[it] = new({"tx_out_", it_str}, this);

            rx_input_data[it]   = new({"rx_input_data_", it_str}, this);
            mvb_discard[it]     = new({"mvb_discard_", it_str}, this);
        end
        rx_out_data     = new("rx_out_data", this);
        rx_out_hdr      = new("rx_out_hdr", this);
    endfunction

    function void build_phase(uvm_phase phase);

        m_model  = model #(CHANNELS, ITEM_WIDTH, META_WIDTH, HDR_WIDTH)::type_id::create("m_model", this);
        tx_input = model_input_fifo#(ITEM_WIDTH, META_WIDTH)::type_id::create("tx_input" , this);
        for (int it = 0; it < CHANNELS; it++) begin
            string it_string;
            it_string.itoa(it);

            tx_compare[it] = uvm_common::comparer_ordered#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH))::type_id::create({"tx_compare_", it_string}, this);
        end

        rx_compare_data = comparer_data #(ITEM_WIDTH, HDR_WIDTH)::type_id::create("rx_compare_data", this);
        rx_compare_meta = comparer_meta #(ITEM_WIDTH, HDR_WIDTH)::type_id::create("rx_compare_meta", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        //TX INPUT
        tx_input_data.connect(tx_input.analysis_export_data);
        tx_input_meta.connect(tx_input.analysis_export_meta);
        tx_input.port.connect(m_model.tx_input.analysis_export);

        //RX INPUT
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            m_model.tx_output[it].connect(tx_compare[it].analysis_imp_model);
            tx_out[it].connect(tx_compare[it].analysis_imp_dut);

            rx_input_data[it].connect(m_model.rx_input[it].analysis_export);
            mvb_discard[it].connect(m_model.rx_discard[it].analysis_export);
        end

        m_model.rx_output.connect(rx_compare_data.analysis_imp_model);
        m_model.rx_output.connect(rx_compare_meta.analysis_imp_model);
        rx_out_data.connect(rx_compare_data.analysis_imp_dut);
        rx_out_hdr.connect(rx_compare_meta.analysis_imp_dut);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= tx_input.used();
        ret |= m_model.used();
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            ret |= tx_compare[it].used();
        end
        ret |= rx_compare_data.used();
        ret |= rx_compare_meta.used();
        return ret;
    endfunction

    function int unsigned success();
        int unsigned ret = 1;
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            ret &= tx_compare[it].success();
        end
        ret &= rx_compare_data.success();
        ret &= rx_compare_meta.success();
        return ret;
    endfunction

    function void report_phase(uvm_phase phase);
        int unsigned total_errors = 0;
        string msg = "";

        // TX path
        for (int unsigned it = 0; it < CHANNELS; it++) begin
            $swrite(msg, "%s\n\tTX path OUTPUT [%0d]: %s", msg, it, tx_compare[it].info());
        end
        $swrite(msg, "%s\n\t---------------------------------------", msg);
        $swrite(msg, "%s\n\tRX path OUTPUT DATA : %s", msg,  rx_compare_data.info());
        $swrite(msg, "%s\n\tRX path OUTPUT META : %s", msg,  rx_compare_meta.info());

        if (this.success() == 1 && this.used() == 0) begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------"}, UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), {msg, "\n\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------"}, UVM_NONE)
        end
    endfunction

endclass
