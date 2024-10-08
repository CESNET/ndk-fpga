//-- monitor.sv: Mfb monitor
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// Definition of mfb monitor
class monitor #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_monitor;

    // ------------------------------------------------------------------------
    // Registration of agent to databaze
    `uvm_component_param_utils(uvm_mfb::monitor #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    // ------------------------------------------------------------------------
    // Parameters
    localparam ITEM_CNT = REGIONS * REGION_SIZE * BLOCK_SIZE;

    // ------------------------------------------------------------------------
    // Variables
    sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) si;

    // ------------------------------------------------------------------------
    // Reference to the virtual interface
    virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH).monitor vif;

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
            si.src_rdy  = vif.monitor_cb.SRC_RDY;
            si.dst_rdy  = vif.monitor_cb.DST_RDY;

            for (int unsigned it = 0; it < REGIONS; it++) begin
                si.sof[it]      = vif.monitor_cb.SOF[it];
                si.eof[it]      = vif.monitor_cb.EOF[it];

                si.data[it]   = vif.monitor_cb.DATA[(it+1)*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH -1 -: REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH];
                if (META_WIDTH > 0) begin
                    si.meta[it]    = vif.monitor_cb.META[(it+1)*META_WIDTH                        -1 -: META_WIDTH];
                end else begin
                    si.meta[it]    = 'x;
                end
                if ($clog2(REGION_SIZE) > 0) begin
                    si.sof_pos[it] = vif.monitor_cb.SOF_POS[(it+1)*$clog2(REGION_SIZE)            -1 -: $clog2(REGION_SIZE)];
                end else begin
                    si.sof_pos[it] = 'x;
                end
                if ($clog2(REGION_SIZE*BLOCK_SIZE) > 0) begin
                    si.eof_pos[it] = vif.monitor_cb.EOF_POS[(it+1)*$clog2(REGION_SIZE*BLOCK_SIZE) -1 -: $clog2(REGION_SIZE*BLOCK_SIZE)];
                end else begin
                    si.eof_pos[it] = 'x;
                end
            end

            // Write sequence item to analysis port.
            si.start[this.get_full_name()] = $time();
            analysis_port.write(si);
        end
    endtask

endclass
