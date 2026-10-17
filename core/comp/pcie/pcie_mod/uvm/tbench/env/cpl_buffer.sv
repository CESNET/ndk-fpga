// cpl_buffer.sv: Check of the completion buffer of the PCIe Hard IP
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

// The completion buffer of the Hard IP holds the completions of all read requests
// that the DUT has sent and that it has not received back yet. One unit of the buffer
// is a 64 B block. A read request takes the units from the 64 B block of its first
// DWORD to the block of its last DWORD. A completion that is not the last one of its
// request releases the units that it fills completely. The last completion releases
// the rest. The check reports an error when the taken units exceed units_max.
class cpl_buffer extends uvm_component;
    `uvm_component_utils(uvm_pcie_top::cpl_buffer)

    localparam int unsigned UNIT_DWORDS = 64/4;

    uvm_analysis_imp_rq #(uvm_pcie::header, cpl_buffer) port_rq;
    uvm_analysis_imp_rc #(uvm_pcie::header, cpl_buffer) port_rc;

    // Size of the buffer in units, 0 disables the check
    int unsigned units_max = 0;

    protected int unsigned units_used = 0;
    protected int unsigned units_used_max = 0;
    // Units that are still taken by each read request, indexed by its tag
    protected int unsigned tag_units[int unsigned];

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        port_rq = new("port_rq", this);
        port_rc = new("port_rc", this);
    endfunction

    // Number of DWORDs in the length field, 0 means 1024
    function int unsigned dwords_get(logic [10-1:0] length);
        return (length == 0) ? 1024 : length;
    endfunction

    function void write_rq(uvm_pcie::header t);
        uvm_pcie::request_header req;
        int unsigned offset;
        int unsigned unit_cnt;

        // Only the memory read requests (MRd) have completions with data
        if (!$cast(req, t) || t.fmt[1] != 1'b0 || t.pcie_type != 5'b00000) begin
            return;
        end

        offset = req.address[6-1:2];
        unit_cnt  = (offset + dwords_get(req.length) + UNIT_DWORDS-1) / UNIT_DWORDS;

        if (tag_units.exists(req.tag)) begin
            `uvm_error(this.get_full_name(), $sformatf(
                "\n\tRead request with tag %0d, which waits for completions already.", req.tag));
        end
        tag_units[req.tag] = unit_cnt;

        units_used += unit_cnt;
        if (units_used > units_used_max) begin
            units_used_max = units_used;
        end
        if (units_max > 0 && units_used > units_max) begin
            `uvm_error(this.get_full_name(), $sformatf(
                "\n\tThe read requests take %0d units of the Hard IP completion buffer of %0d units.",
                units_used, units_max));
        end
    endfunction

    function void write_rc(uvm_pcie::header t);
        uvm_pcie::completer_header cpl;
        int unsigned offset;
        int unsigned dwords;
        int unsigned unit_cnt;
        logic last;

        if (!$cast(cpl, t) || !tag_units.exists(cpl.tag)) begin
            return;
        end

        // The completion is the last one when the remaining bytes fit in its length.
        // A completion without data ends the request too.
        offset = cpl.lower_address[6-1:2];
        dwords = dwords_get(cpl.length);
        last   = (cpl.fmt[1] == 1'b0) || (((cpl.byte_count + cpl.lower_address[2-1:0] + 3) / 4) <= dwords);

        unit_cnt = last ? tag_units[cpl.tag] : (offset + dwords) / UNIT_DWORDS;
        if (unit_cnt > tag_units[cpl.tag]) begin
            `uvm_error(this.get_full_name(), $sformatf(
                "\n\tCompletion with tag %0d releases more units than its read request took.", cpl.tag));
            unit_cnt = tag_units[cpl.tag];
        end

        units_used         -= unit_cnt;
        tag_units[cpl.tag] -= unit_cnt;
        if (last) begin
            tag_units.delete(cpl.tag);
        end
    endfunction

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), $sformatf(
            "\n\tHard IP completion buffer: at most %0d of %0d units taken", units_used_max, units_max), UVM_NONE);
    endfunction
endclass
