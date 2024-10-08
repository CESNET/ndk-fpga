/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
 */

class ifg_config;
    rand bit enabled;
    rand int unsigned length;

    int unsigned ifg_enabled  = 0;
    int unsigned ifg_disabled = 1;
    int unsigned ifg_low      = 0;
    int unsigned ifg_high     = 18;

    constraint cDelayBase {
        enabled dist {1'b1 := ifg_enabled, 1'b0 := ifg_disabled};
        length  inside {[ifg_low:ifg_high]};
    }
endclass

///////////////////////////////////////////////////////////////////////////////
// this driver drive send only rdy signals on avalon tx bus
class driver#(REGIONS) extends sv_common_pkg::Responder;

    ////////////////////
    // Variables
    virtual avst_rx_if#(REGIONS).driver vif;
    //config object...
    config_item      cfg;
    ifg_config  vld_cfg;

    //////////////////////////
    // functions
    function new(string inst, virtual avst_rx_if #(REGIONS) vif, config_item cfg = null);
        super.new(inst);
        this.vif = vif;
        if (cfg != null) begin
            this.cfg = cfg;
        end else begin
            this.cfg = new();
        end

        this.vld_cfg = new();
    endfunction

    function void verbosity_set(int unsigned level);
    endfunction

    function void ifg_set(ifg_config vld);
        vld_cfg = vld;
    endfunction

    // Drive and wait on the bus
    task run();
        vif.driver_cb.ready <= '0;
        @(vif.driver_cb);

        //drive
        forever begin
            int unsigned max_delay;
            assert(this.vld_cfg.randomize());

            if(vif.driver_cb.RESET == 1'b1) begin
                vif.driver_cb.ready <= 1'b0;
                //wait for clock
                @(vif.driver_cb);
            end else begin
                vif.driver_cb.ready <= 1'b1;
                //wait for clock
                @(vif.driver_cb);

                if (this.vld_cfg.enabled == 1'b1) begin
                    max_delay = this.cfg.wait_delay > this.vld_cfg.length ? this.cfg.wait_delay : this.vld_cfg.length;
                    for (int unsigned it = 0; it < max_delay; it++) begin
                        vif.driver_cb.ready <= 1'b0;
                        //wait for clock
                        @(vif.driver_cb);
                    end
                end
            end
        end
    endtask
endclass
