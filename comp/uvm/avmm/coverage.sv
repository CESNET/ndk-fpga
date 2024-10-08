// coverage.sv: Coverage for AVMM interface
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class coverage #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_avmm::coverage #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // ----------- //
    // Input ports //
    // ----------- //

    `uvm_analysis_imp_decl(_slave)
    `uvm_analysis_imp_decl(_master)

    typedef coverage #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) this_type;
    uvm_analysis_imp_slave  #(sequence_item_response #(DATA_WIDTH), this_type)                            analysis_export_slave;
    uvm_analysis_imp_master #(sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH), this_type) analysis_export_master;

    // ----------- //
    // Covergroups //
    // ----------- //

    // Slave
    covergroup readdata_covergroup with function sample(sequence_item_response #(DATA_WIDTH) item);
        readdata : coverpoint item.readdata iff (item.readdatavalid === 1'b1) {
            bins zero    = {0};
            bins nonzero = {[1 : 2**DATA_WIDTH-1]};
        }
    endgroup

    covergroup ready_covergroup with function sample(sequence_item_response #(DATA_WIDTH) item);
        ready : coverpoint item.ready {
            bins short   = (0 => 1 => 0);
            bins longer  = (0 => 1[*2:16]  => 0);
            bins long    = (0 => 1[*17:32] => 0);
            bins longest = default;
        }
    endgroup

    // Master
    covergroup request_validity_covergroup with function sample(sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) item);
        validity : coverpoint item.ready {
            bins valid   = {1};
            bins invalid = {0};
        }

        read : coverpoint item.read {
            bins read    = {1};
            bins nonread = {0};
        }
        write : coverpoint item.write {
            bins write    = {1};
            bins nonwrite = {0};
        }

        valid_read : cross validity, read;
        valid_write : cross validity, write;
    endgroup

    // Constructor
    function new(string name = "coverage", uvm_component parent = null);
        super.new(name, parent);

        analysis_export_slave  = new("analysis_export_slave", this);
        analysis_export_master = new("analysis_export_master", this);

        readdata_covergroup         = new();
        ready_covergroup            = new();
        request_validity_covergroup = new();
    endfunction

    // Response item
    function void write_slave(sequence_item_response #(DATA_WIDTH) t);
        readdata_covergroup.sample(t);
        ready_covergroup   .sample(t);
    endfunction

    // Request item
    function void write_master(sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) t);
        request_validity_covergroup.sample(t);
    endfunction

    function void report_phase(uvm_phase phase);
        string report_message_slave;
        string report_message_master;
        super.report_phase(phase);

        report_message_slave  = $sformatf("\n\tREADDATA coverage %0f %%\n\tREADY coverage %0f %%\n", readdata_covergroup.get_inst_coverage(), ready_covergroup.get_inst_coverage());
        report_message_master = $sformatf("\n\tRequest coverage %0f %%\n", request_validity_covergroup.get_inst_coverage());

        `uvm_info(this.get_full_name(), { report_message_slave, "\n", report_message_master } , UVM_LOW);
    endfunction

endclass
