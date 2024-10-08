//-- monitor.sv: AVST monitor
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of mfb monitor
class monitor #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_monitor;

    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_component_param_utils(uvm_avst::monitor #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    // ------------------------------------------------------------------------
    // Parameters
    localparam ITEM_CNT = REGIONS * REGION_SIZE * BLOCK_SIZE;

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) si;

    // ------------------------------------------------------------------------
    // Reference to the virtual interface
    virtual avst_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH).monitor vif;

    // ------------------------------------------------------------------------
    // Analysis port used to send transactions to all connected components.
    uvm_analysis_port #(sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)) analysis_port;

    // ------------------------------------------------------------------------
    // Constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // ------------------------------------------------------------------------
    // Functions
    function void build_phase(uvm_phase phase);
        analysis_port = new("analysis port", this);
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            @(vif.monitor_cb);

            si = sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("si");
            si.ready = vif.monitor_cb.READY;

            for (int unsigned it = 0; it < REGIONS; it++) begin
                si.sop[it]   = vif.monitor_cb.SOP[it];
                si.eop[it]   = vif.monitor_cb.EOP[it];
                si.valid[it] = vif.monitor_cb.VALID[it];

                si.data[it]  = vif.monitor_cb.DATA[(it+1)*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH -1 -: REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH];
                si.meta[it]  = vif.monitor_cb.META[(it+1)*META_WIDTH                        -1 -: META_WIDTH];
                si.empty[it] = vif.monitor_cb.EMPTY[(it+1)*$clog2(REGION_SIZE*BLOCK_SIZE)   -1 -: $clog2(REGION_SIZE*BLOCK_SIZE)];
            end

            // Write sequence item to analysis port.
            si.start[this.get_full_name()] = $time();
            analysis_port.write(si);
        end
    endtask

endclass
