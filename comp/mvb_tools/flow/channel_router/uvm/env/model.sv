/*
 * file       : model.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Model for mvb channel router
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class model_data;
    int unsigned act = 0;
endclass

class reg_cbs extends uvm_reg_cbs;

    model_data data;

    function new(model_data data);
        this.data = data;
    endfunction

    virtual task post_write(uvm_reg_item rw);
        // OPT_MODE = true
        data.act = 0;
        // OPT_MODE = false
        //data.act = rw.value[0];
    endtask
endclass

class model#(INPUT_CHANNELS, OUTPUT_CHANNELS, RESET_TYPE, OPT_MODE) extends uvm_component;
    `uvm_component_param_utils(uvm_channel_router::model#(INPUT_CHANNELS, OUTPUT_CHANNELS, RESET_TYPE, OPT_MODE))

    local regmodel#(INPUT_CHANNELS, OUTPUT_CHANNELS, RESET_TYPE) m_regmodel;
    local model_data channel[INPUT_CHANNELS];
    local reg_cbs    cbs[INPUT_CHANNELS];
   //local int unsigned channel_act[INPUT_CHANNELS]  = '{INPUT_CHANNELS{0}};

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        for (int unsigned it = 0; it < INPUT_CHANNELS; it++) begin
            channel[it] = new();
            cbs[it]     = new(channel[it]);
        end
    endfunction

    function void regmodel_set(regmodel#(INPUT_CHANNELS, OUTPUT_CHANNELS, RESET_TYPE) m_regmodel);
        this.m_regmodel = m_regmodel;
        for (int unsigned it = 0; it < INPUT_CHANNELS; it++) begin
            uvm_reg_field_cb::add(this.m_regmodel.channel[it].ch_min, cbs[it]);
        end
    endfunction

    function int unsigned port_get(int unsigned input_port);
        string msg;
        int unsigned ret;

        if (input_port >= INPUT_CHANNELS) begin
            string msg;

            msg = $sformatf( "\n\tChannel %0d is out of boud [0:%0d]", input_port, INPUT_CHANNELS);
            `uvm_error(this.get_full_name(), msg);
            return 0;
        end

        if (m_regmodel.channel[input_port].incr.get() == 0) begin
            ret = input_port;
        end else begin
            if (OPT_MODE == 1) begin
                int ch_diff;
                ret = channel[input_port].act + m_regmodel.channel[input_port].ch_min.get();
                ch_diff = (m_regmodel.channel[input_port].ch_max.get() - m_regmodel.channel[input_port].ch_min.get());
                channel[input_port].act = (channel[input_port].act + m_regmodel.channel[input_port].incr.get()) & (ch_diff);
            end else begin
                int ch_next;
                ret = channel[input_port].act;
                ch_next = channel[input_port].act + m_regmodel.channel[input_port].incr.get();
                if ((ch_next <= m_regmodel.channel[input_port].ch_max.get()) && (ch_next < OUTPUT_CHANNELS) && (ch_next >= m_regmodel.channel[input_port].ch_min.get())) begin
                    channel[input_port].act = ch_next;
                end else begin
                    channel[input_port].act = m_regmodel.channel[input_port].ch_min.get();
                end
            end
        end


        msg = $sformatf( "\n\tInput channel %0d output channel %0d", input_port, ret);
        `uvm_info(this.get_full_name(), msg, UVM_DEBUG);
        return ret;
    endfunction

    function void reset();
        m_regmodel.reset();
        for (int unsigned it = 0; it < INPUT_CHANNELS; it++) begin
            if (OPT_MODE == 1) begin
                channel[it].act = 0;
            end else begin
                case (RESET_TYPE)
                    0 :  channel[it].act = 0;
                    1 :  channel[it].act = 0;
                    2 :  channel[it].act = OUTPUT_CHANNELS/INPUT_CHANNELS*it;
                    default : `uvm_fatal(this.get_full_name(), "\n\tUnknown reset type")
                endcase
            end
        end
    endfunction
endclass

