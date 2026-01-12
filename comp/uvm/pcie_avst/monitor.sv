// monitor.sv: pcie monitor
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class monitor#(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned META_WIDTH,
    logic STRADDLING,
    direction_t dir
) extends uvm_pcie::monitor;
    `uvm_component_param_utils(uvm_pcie_avst::monitor#(REGIONS, REGION_SIZE, META_WIDTH, STRADDLING, dir));

    localparam int unsigned ITEM_WIDTH = 32;

    typedef monitor#(REGIONS, REGION_SIZE, META_WIDTH, STRADDLING, dir) this_type;
    uvm_analysis_imp#(uvm_avst::sequence_item #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH), this_type) port_avst;


    protected logic [32-1:0]  data[$];
    protected logic [128-1:0] hdr;
    protected logic [32-1:0]  prefix;
    protected logic [3-1:0]   bar;
    protected logic [1-1:0]   error;
    time                      time_start;

    // protected variable
    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        port_avst = new("port_avst", this);
    endfunction


    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
    endfunction

    virtual function void write(uvm_avst::sequence_item #(REGIONS, REGION_SIZE, 32, META_WIDTH) t);

        // If reset ocurres then reset all data
        if (reset_sync.has_been_reset()) begin
            data.delete();
        end

        if ($isunknown(t.valid) || reset_sync.is_reset()) begin
            return;
        end

        assert (
            // If frame is not valid then dont care
            (|t.valid)  == 1'b0 ||
            // There cannot be error when there is one region
            (REGIONS == 1)      ||
            // When STRADDLING is off then packet can start only in first region
            (STRADDLING == 1'b0 && (|t.sop[REGIONS-1:1]) == 0) ||
            // When STRADDLING is on then packet can start in region only when previous packet end in previous region
            // or in first region
            (STRADDLING == 1'b1 && (|(t.sop[REGIONS-1:1] & ~t.eop[REGIONS-2:0])) == 0)
        ) else begin
            string msg;

            msg = $sformatf("\n\tWrong position of SOP.\n\tSTRADDLING %0d SOP %b EOP %b VALID %b", STRADDLING, t.sop, t.eop, t.valid);
            `uvm_error(this.get_full_name(), msg);
        end

        for (int unsigned it = 0; it < REGIONS; it++) begin
            if (t.valid[it] == 1'b1) begin
                if (data.size() == 0 && t.sop[it] == 1) begin
                    case(dir)
                        AVST_UP: begin
                            bar = 0;
                            {error, prefix, hdr} = t.meta[it];
                        end

                        AVST_DOWN: begin
                            error = 0;
                            {bar, prefix, hdr} = t.meta[it];
                        end

                        default begin
                            `uvm_fatal(this.get_full_name(), "\n\tUNKNOWN DIRECTION");
                        end
                    endcase
                    time_start = $time;
                end

                if (t.eop[it] == 1) begin
                    uvm_pcie::header pcie_hdr;
                    const int unsigned jt_end = REGION_SIZE - t.empty[it];

                    for (int unsigned jt = 0; jt < jt_end;) begin
                         jt++;
                         data.push_back(t.data[it][jt*ITEM_WIDTH-1 -: ITEM_WIDTH]);
                    end
                    pcie_hdr = hdr_get(hdr, prefix, error, bar, data, bar_cfg, this);
                    data.delete();

                    pcie_hdr.time_add(this.get_full_name(), time_start);
                    analysis_port.write(pcie_hdr);
                end else begin
                    for (int unsigned jt = 0; jt < REGION_SIZE;) begin
                         jt++;
                         data.push_back(t.data[it][jt*ITEM_WIDTH-1 -: ITEM_WIDTH]);
                    end
                end
            end
        end

    endfunction
endclass


