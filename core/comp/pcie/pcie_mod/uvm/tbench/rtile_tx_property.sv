// rtile_tx_property.sv: Rules of the R-Tile TX interface
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"

// One region of the interface is one segment of the R-Tile TX interface in the
// double-width mode. The module checks these rules:
// - VALID is high only in the cycle after READY was high.
// - A TLP has no cycle with VALID low between SOP and EOP. A cycle after READY
//   was low does not count.
// - A TLP starts only in segments st0 and st2 (4 regions) or st0 and st1 (2 regions).
// - A TLP that starts in a higher segment ends in the same word.
// See the R-Tile Avalon-ST IP for PCIe User Guide (683501), Tables 59 and 60.
module rtile_tx_property #(
    int unsigned REGIONS
) (
    input logic RESET,
    avst_if     vif
);
    localparam int unsigned SOP_STEP = (REGIONS > 1) ? REGIONS/2 : 1;

    string module_name = $sformatf("%m");

    logic        ready_reg = 1'b0;
    logic        tlp_open  = 1'b0;
    int unsigned sop_region;

    always @(vif.monitor_cb) begin
        if (RESET !== 1'b0) begin
            tlp_open = 1'b0;
        end else if (ready_reg !== 1'b1) begin
            if (vif.monitor_cb.VALID !== '0) begin
                `uvm_error(module_name, $sformatf("\n\tVALID 'b%b in the cycle after READY was low.",
                                                  vif.monitor_cb.VALID));
            end
        end else begin
            for (int unsigned r = 0; r < REGIONS; r++) begin
                if (vif.monitor_cb.VALID[r] !== 1'b1) begin
                    if (tlp_open) begin
                        `uvm_error(module_name, $sformatf("\n\tVALID is low in region %0d inside a TLP.", r));
                        tlp_open = 1'b0;
                    end
                    continue;
                end
                if (vif.monitor_cb.SOP[r] === 1'b1) begin
                    if ((r % SOP_STEP) != 0) begin
                        `uvm_error(module_name, $sformatf("\n\tSOP in region %0d, which R-Tile does not allow.", r));
                    end
                    tlp_open   = 1'b1;
                    sop_region = r;
                end
                if (vif.monitor_cb.EOP[r] === 1'b1) begin
                    tlp_open = 1'b0;
                end
            end
            if (tlp_open && sop_region != 0) begin
                `uvm_error(module_name, $sformatf("\n\tThe TLP that starts in region %0d does not end in the word.",
                                                  sop_region));
            end
        end
        ready_reg = vif.monitor_cb.READY;
    end
endmodule
