// scoreboard_cmp.sv: Scoreboard comparer
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kříž <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

let abs(a) = (a < 0) ? -a : a;

class delayer_cmp #(MFB_ITEM_WIDTH, TIMESTAMP_WIDTH) extends uvm_common::comparer_base_unordered#(uvm_timestamp_limiter::ts_limiter_item#(MFB_ITEM_WIDTH, TIMESTAMP_WIDTH), uvm_logic_vector_array::sequence_item#(MFB_ITEM_WIDTH));
    `uvm_component_param_utils(uvm_timestamp_limiter::delayer_cmp #(MFB_ITEM_WIDTH, TIMESTAMP_WIDTH))

    protected DUT_ITEM times2cmp[$];
    protected logic [TIMESTAMP_WIDTH-1 : 0] dut_ts;
    protected uvm_common::stats             ts_stats;
    protected DUT_ITEM tr_dut_first;
    protected DUT_ITEM tr_dut_second;
    int fd;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        ts_stats  = new();
        fd = $fopen("ts_file.csv");
        $fwrite(fd, "DUT_TS,MODEL_TS,SIZE,INPUT_PKT_TIME\n");
    endfunction

    virtual function int unsigned compare(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        string msg = "";
        msg = message(tr_model, tr_dut);
        times2cmp.push_back(tr_dut);
        if (times2cmp.size == 2) begin
            tr_dut_first = times2cmp.pop_front();
            tr_dut_second = times2cmp.pop_front();
            dut_ts = tr_dut_second.time_last() - tr_dut_first.time_last();
            times2cmp.push_back(tr_dut_second);

            // msg = {msg, $sformatf("DUT TS %0.2f\n",  (dut_ts/1ns))};
            // msg = {msg, $sformatf("SIZE OF TR %0d\n",  tr_model.item.data_tr.size())};
            $fwrite(fd,"%0.2f, %0.2f, %d, %0.2f, \n", dut_ts/1ns, tr_model.timestamp, tr_model.data_tr.size(), tr_model.time_last()/1ns);
            ts_stats.next_val(abs(signed'(tr_model.timestamp - dut_ts/1ns)));
        end
        `uvm_info(get_type_name(), msg, UVM_MEDIUM)
        return tr_model.data_tr.compare(tr_dut);
    endfunction

    virtual function string message(MODEL_ITEM tr_model, DUT_ITEM tr_dut);
        string msg = "\n";
        msg = {msg, $sformatf("\n\tDUT PACKET %s\n\n",  tr_dut.convert2string())};
        msg = {msg, $sformatf("\n\tMODEL PACKET%s\n\n",  tr_model.data_tr.convert2string())};
        // msg = {msg, $sformatf("tr_dut.in_time %0.2f\n",  tr_dut.in_time/1ns)};
        msg = {msg, $sformatf("tr_model timestamp %0.2f\n",  tr_model.timestamp)};
        return msg;
    endfunction

    function void report_phase(uvm_phase phase);
        real min;
        real max;
        real avg;
        real std_dev;
        super.report_phase(phase);
        $fclose(fd);
        ts_stats.count(min, max, avg, std_dev);
        $write("min %0.2f, max %0.2f, avg %0.2f, std_dev %0.2f\n", min, max, avg, std_dev);
    endfunction
endclass
