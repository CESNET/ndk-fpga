// discarder.sv: Retrieves the discard events from the dut
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class discarder #(int unsigned MFB_REGIONS) extends uvm_component;
    `uvm_component_param_utils(frame_masker::discarder #(MFB_REGIONS))

    localparam string DUT_PATH = "testbench.DUT_U.VHDL_DUT_U";

    uvm_analysis_port #(bit) analysis_port;

    protected frame_masker::probe_cbs #(MFB_REGIONS) probe_callback;

    function new(string name = "discarder", uvm_component parent = null);
        super.new(name, parent);

        analysis_port = new("analysis_port", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        probe_callback = frame_masker::probe_cbs #(MFB_REGIONS)::type_id::create("probe_callback", this);
        uvm_probe::pool::get_global_pool().get({"probe_event_component_", DUT_PATH, ".probe_mask2discard"}).add_callback(probe_callback);
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            bit discard;

            probe_callback.get_discard(discard);
            analysis_port.write(discard);
        end
    endtask

endclass
