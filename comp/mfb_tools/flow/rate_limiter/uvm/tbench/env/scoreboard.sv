// scoreboard.sv: Scoreboard for verification
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Tomas Hak <xhakto01@vut.cz>

// SPDX-License-Identifier: BSD-3-Clause

class scoreboard#(MFB_ITEM_WIDTH, MFB_META_WIDTH, INTERVAL_COUNT, SHAPING_TYPE, CLK_PERIOD) extends uvm_scoreboard;
    `uvm_component_param_utils(uvm_rate_limiter::scoreboard#(MFB_ITEM_WIDTH, MFB_META_WIDTH, INTERVAL_COUNT, SHAPING_TYPE, CLK_PERIOD))

    uvm_analysis_export#(uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH)) analysis_export_rx_packet;
    uvm_analysis_export#(uvm_logic_vector::sequence_item#(MFB_META_WIDTH))       analysis_export_rx_meta;
    uvm_analysis_export#(uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH)) analysis_export_tx_packet;
    uvm_analysis_export#(uvm_logic_vector::sequence_item#(MFB_META_WIDTH))       analysis_export_tx_meta;

    local uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH)) dut_input;
    local uvm_tlm_analysis_fifo#(uvm_logic_vector::sequence_item#(MFB_META_WIDTH))       dut_input_meta;
    local uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH)) dut_output;
    local uvm_tlm_analysis_fifo#(uvm_logic_vector::sequence_item#(MFB_META_WIDTH))       dut_output_meta;

    regmodel#(INTERVAL_COUNT) m_regmodel;

    protected int unsigned speed_test_bytes = 0;
    protected int unsigned speed_test_pkts = 0;

    protected int unsigned section_length;
    protected int unsigned interval_length;
    protected int unsigned interval_speed [INTERVAL_COUNT/2];

    semaphore sem;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        analysis_export_rx_packet = new("analysis_export_rx_packet", this);
        analysis_export_rx_meta   = new("analysis_export_rx_meta"  , this);
        analysis_export_tx_packet = new("analysis_export_tx_packet", this);
        analysis_export_tx_meta   = new("analysis_export_tx_meta"  , this);
        dut_input                 = new("dut_input"                , this);
        dut_input_meta            = new("dut_input_meta"           , this);
        dut_output                = new("dut_output"               , this);
        dut_output_meta           = new("dut_output_meta"          , this);
        sem                       = new(1);
    endfunction

    function void connect_phase(uvm_phase phase);
        analysis_export_rx_packet.connect(dut_input.analysis_export);
        analysis_export_rx_meta.connect(dut_input_meta.analysis_export);
        analysis_export_tx_packet.connect(dut_output.analysis_export);
        analysis_export_tx_meta.connect(dut_output_meta.analysis_export);
    endfunction

    function void regmodel_set(regmodel#(INTERVAL_COUNT) m_regmodel);
        this.m_regmodel = m_regmodel;
    endfunction

    function void read_config_regs();
        section_length  = m_regmodel.get_reg_by_name("section").get();
        interval_length = m_regmodel.get_reg_by_name("interval").get();
        // only half of the registers get configured (to test looping from the first register)
        for (int i = 0; i < INTERVAL_COUNT/2; i++) begin
            interval_speed[i] = m_regmodel.get_reg_by_name({"speed_", i}).get();
        end
    endfunction

    function real conv_Bscn2Gbs(int unsigned Bscn, int unsigned sec_len);
        real clk_period = (CLK_PERIOD*2) / 64'd1_000_000_000_000;
        real clk_freq   = 1 / (clk_period);
        return (Bscn * 8) * (clk_freq / sec_len) / 1_000_000_000;
    endfunction

    function int unsigned conv_Gbs2Bscn(real Gbs, int unsigned sec_len);
        real clk_period = (CLK_PERIOD*2) / 64'd1_000_000_000_000;
        real clk_freq   = 1 / (clk_period);
        return (Gbs / 8.0) / (clk_freq / sec_len) * 1_000_000_000;
    endfunction

    function real conv_Pscn2Ps(int unsigned Pscn, int unsigned sec_len);
        real clk_period = (CLK_PERIOD*2) / 64'd1_000_000_000_000;
        real clk_freq   = 1 / (clk_period);
        return Pscn * (clk_freq / sec_len);
    endfunction

    function int unsigned conv_Ps2Pscn(real Ps, int unsigned sec_len);
        real clk_period = (CLK_PERIOD*2) / 64'd1_000_000_000_000;
        real clk_freq   = 1 / (clk_period);
        return Ps / (clk_freq / sec_len);
    endfunction

    task change_mbytes(int unsigned new_value);
        sem.get(1);
        if (new_value == 0) begin
            speed_test_bytes = new_value;
            speed_test_pkts = new_value;
        end else begin
            speed_test_bytes += new_value;
            speed_test_pkts += 1;
        end
        sem.put(1);
    endtask

    task measuring();
        int unsigned interval_pointer  = 0;

        // time variables
        time speed_test_time = interval_length*section_length*CLK_PERIOD*2;
        time speed_test_start = 400ns;
        time speed_meter_duration;
        time time_act;

        // common measurement variables
        real act_speed_section;
        real act_speed_second;
        real exp_speed_section;
        real exp_speed_second;
        real speed_var_section;
        real speed_var_second;
        real speed_lim_section;
        real speed_lim_second;
        // bytes and packets are counted only after the whole packet is received
        // this can cause speed measurement errors
        real speed_tolerance;

        // report strings
        string speed_s;
        string speed_bytes_s = "Gb/s";
        string speed_pkts_s = "pkts/s";

        forever begin
            time_act = $time();
            speed_meter_duration = time_act - speed_test_start;
            if (speed_meter_duration >= speed_test_time) begin

                // measurement
                exp_speed_section = interval_speed[interval_pointer];
                if (SHAPING_TYPE == 0) begin
                    act_speed_section = real'(speed_test_bytes)/interval_length;
                    act_speed_second  = conv_Bscn2Gbs(act_speed_section, section_length);
                    exp_speed_second  = conv_Bscn2Gbs(exp_speed_section, section_length);
                    speed_var_section = exp_speed_section - act_speed_section;
                    speed_var_second  = conv_Bscn2Gbs((speed_var_section < 0) ? -speed_var_section : speed_var_section, section_length);
                    speed_tolerance   = real'(conv_Gbs2Bscn(0.1, section_length));
                    speed_lim_second  = 5.0;
                    speed_lim_section = conv_Gbs2Bscn(speed_lim_second, section_length);
                    speed_s           = speed_bytes_s;
                end else begin
                    act_speed_section = real'(speed_test_pkts)/interval_length;
                    act_speed_second  = conv_Pscn2Ps(act_speed_section, section_length);
                    exp_speed_second  = conv_Pscn2Ps(exp_speed_section, section_length);
                    speed_var_section = exp_speed_section - act_speed_section;
                    speed_var_second  = conv_Pscn2Ps((speed_var_section < 0) ? -speed_var_section : speed_var_section, section_length);
                    speed_tolerance   = 1.0;
                    speed_lim_section = 5.0;
                    speed_lim_second  = conv_Pscn2Ps(speed_lim_section, section_length);
                    speed_s           = speed_pkts_s;
                end

                // report
                `uvm_info(this.get_full_name(), $sformatf("Speed = %7.3f / %7.3f [%s] (Variance = %.3f [%s])", act_speed_second, exp_speed_second, speed_s, speed_var_second, speed_s), UVM_NONE)
                if (speed_var_section < 0 && speed_var_section >= -speed_tolerance) begin
                    `uvm_info(this.get_full_name(), $sformatf("Limit exceeded a little! (probably due to measurement error)"), UVM_NONE)
                end else if (speed_var_section < -speed_tolerance) begin
                    `uvm_error(this.get_full_name(), $sformatf("Limit exceeded too much!"))
                end else if (speed_var_section >= speed_lim_section) begin
                    `uvm_error(this.get_full_name(), $sformatf("Too slow! (Variance = %.3f / %.3f [%s]).", speed_var_second, speed_lim_second, speed_s))
                end

                // preparation
                speed_test_start = time_act;
                change_mbytes(0);
                interval_pointer = (interval_pointer == $size(interval_speed)-1)? 0 : interval_pointer+1;
            end
            #(CLK_PERIOD);
        end
    endtask

    task run_phase(uvm_phase phase);

        uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH) tr_dut_in;
        uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH) tr_dut_out;
        uvm_logic_vector::sequence_item#(MFB_META_WIDTH)       tr_dut_in_meta;
        uvm_logic_vector::sequence_item#(MFB_META_WIDTH)       tr_dut_out_meta;

        #(400ns)

        read_config_regs();

        fork
            measuring();
        join_none

        forever begin
            dut_output.get(tr_dut_out);
            dut_output_meta.get(tr_dut_out_meta);

            change_mbytes(tr_dut_out.data.size());

            dut_input.get(tr_dut_in);
            dut_input_meta.get(tr_dut_in_meta);

            if (tr_dut_in.compare(tr_dut_out) == 0 || tr_dut_in_meta.compare(tr_dut_out_meta) == 0) begin
                string msg;
                msg = $sformatf( "\n\tCheck packet failed.\n\n\tInput packet\n%s\n%s\n\n\tOutput packet\n%s\n%s", tr_dut_in_meta.convert2string(), tr_dut_in.convert2string(), tr_dut_out_meta.convert2string(), tr_dut_out.convert2string());
                `uvm_error(this.get_full_name(), msg);
            end
        end
    endtask

    function int unsigned used();
        int unsigned ret = 0;
        ret |= dut_input.used();
        ret |= dut_input_meta.used();
        ret |= dut_output.used();
        ret |= dut_output_meta.used();
        return ret;
    endfunction

    function void report_phase(uvm_phase phase);

        if (this.used() == 0) begin
            `uvm_info(get_type_name(), "\n\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------", UVM_NONE)
        end else begin
            `uvm_info(get_type_name(), "\n\n\t---------------------------------------\n\t----     VERIFICATION FAILED       ----\n\t---------------------------------------", UVM_NONE)
        end

    endfunction

endclass
