// testbench.sv: Testbench
// MVB_FORK UVM verification
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"
import test::*;

module testbench;

    // Signals
    logic CLK = 0;

    // Interfaces
    reset_if reset(CLK);
    mvb_if #(
        .ITEMS      (ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH)
    ) mvb_wr(CLK);
    mvb_if #(
        .ITEMS      (ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH)
    ) mvb_rd[OUTPUT_PORTS](CLK);

    // clock period
    always begin
        #(CLK_PERIOD) CLK = ~CLK;
    end

    // Start of tests
    genvar i;
    generate for (i = 0; i < OUTPUT_PORTS; i++) begin : gen_cfg
        initial begin
            uvm_config_db#(virtual mvb_if#(.ITEMS(ITEMS), .ITEM_WIDTH(ITEM_WIDTH)))::set(
                null, "", $sformatf("vif_tx_%0d", i), mvb_rd[i]);
        end
    end endgenerate

    initial begin
        uvm_root m_root;
        // Configuration of database
        uvm_config_db#(virtual reset_if)::set(null, "", "vif_reset", reset);
        uvm_config_db#(virtual mvb_if#(.ITEMS(ITEMS), .ITEM_WIDTH(ITEM_WIDTH)))::set(null, "", "vif_rx", mvb_wr);

        m_root = uvm_root::get();
        m_root.finish_on_completion = 0;
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

    // dut
    dut DUT_U (
        .CLK    (CLK),
        .RST    (reset.RESET),
        .mvb_wr (mvb_wr),
        .mvb_rd (mvb_rd)
    );

    // Properties
    mvb_property #(
        .ITEMS      (ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH)
    )
    property_wr (
        .RESET (reset.RESET),
        .vif   (mvb_wr)
    );

    // The DUT is on the "SRC" side of mvb_rd. In the "logic" and "simple"
    // builds a port's SRC_RDY is gated with the AND of all ports' DST_RDY, so
    // it may drop while that port's own DST_RDY is low - the hold check of
    // mvb_property is not valid for these builds (only "register" guarantees
    // per-port independence).
    generate for (i = 0; i < OUTPUT_PORTS; i++) begin : gen_prop
        if (VERSION == "logic" || VERSION == "simple") begin : gen_prop_no_hold
            mvb_property_no_hold #(
                .ITEMS      (ITEMS),
                .ITEM_WIDTH (ITEM_WIDTH)
            )
            property_rd (
                .RESET (reset.RESET),
                .vif   (mvb_rd[i])
            );
        end else begin : gen_prop_full
            mvb_property #(
                .ITEMS      (ITEMS),
                .ITEM_WIDTH (ITEM_WIDTH)
            )
            property_rd (
                .RESET (reset.RESET),
                .vif   (mvb_rd[i])
            );
        end
    end endgenerate

endmodule
