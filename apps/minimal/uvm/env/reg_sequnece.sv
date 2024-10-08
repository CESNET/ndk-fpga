/*
 * file       : sequence.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: sequence for application core register model
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class reg_sequence#(STREAMS, CHANNELS, DMA_STREAMS, DMA_RX_CHANNELS) extends uvm_sequence;
    `uvm_object_param_utils(uvm_app_core_minimal::reg_sequence#(STREAMS, CHANNELS, DMA_STREAMS, DMA_RX_CHANNELS))

    localparam APP_RX_CHANNELS = DMA_RX_CHANNELS/(STREAMS/DMA_STREAMS);

    uvm_app_core::regmodel m_regmodel;

    function new (string name = "reg_sequence");
        super.new(name);
    endfunction

    task body();
        regmodel #(STREAMS, CHANNELS, DMA_STREAMS, DMA_RX_CHANNELS) m_regmodel_minimal;
        string msg;
        uvm_status_e   status;
        uvm_reg_data_t data;
        uvm_reg        regs[$];

        if ($cast(m_regmodel_minimal, m_regmodel) == 0) begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot convert reg model to uvm_app_core_minimal::regmodel.");
        end

        for (int unsigned it = 0; it < STREAMS; it++) begin
            for (int unsigned jt = 0; jt < CHANNELS; jt++) begin
                if(!m_regmodel_minimal.stream[it].channel[jt].randomize() with {ch_min.value <= ch_max.value; ch_max.value < APP_RX_CHANNELS; incr.value dist {[0:5] :/ 30, [6:255] :/ 1};
                $countones(ch_max.value-ch_min.value+1) <= 1;}) begin
                    `uvm_fatal(m_regmodel_minimal.get_full_name(), "\n\treg_sequence cannot randomize");
                end

                $swrite(msg, "%s\n\t\tPORT [%0d] CHANNEL [%0d] :  min %0d max %0d inc %0d", msg, it, jt, m_regmodel_minimal.stream[it].channel[jt].ch_min.value, m_regmodel_minimal.stream[it].channel[jt].ch_max.value, m_regmodel_minimal.stream[it].channel[jt].incr.value);
            end
        end
        `uvm_info(this.get_full_name(), {msg, "\n"}, UVM_LOW);

        //update in defined order
        //m_regmodel.update(status);
        //update in random order
        m_regmodel_minimal.get_registers(regs);
        regs.shuffle();
        foreach (regs[it]) begin
            regs[it].update(status);
        end

		//just for synchronization
        m_regmodel_minimal.stream[0].channel[0].read(status, data, .parent(this));
    endtask
endclass


