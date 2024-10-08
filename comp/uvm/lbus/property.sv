// property.sv: Properties for the LBUS interface
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`include "uvm_macros.svh"
import uvm_pkg::*;

module lbus_property
    (
        input RESET,
        lbus_if vif
    );
    string module_name = "";
    logic START = 1'b1;

    // Start check properties after first clock
    initial begin
        $sformat(module_name, "%m");
        @(posedge vif.CLK)
        #(10ps)
        START = 1'b0;
    end

    // ========== //
    // Properties //
    // ========== //

    // --------------- //
    // Signal validity //
    // --------------- //

    // RDY must be always valid
    property valid_rdy;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        !$isunknown(vif.RDY);
    endproperty

    // ENA must be always valid if the RDY is valid
    property valid_ena;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        vif.RDY |-> !$isunknown(vif.ENA);
    endproperty

    // DATA must be always valid if the ENA is valid
    property valid_data (int unsigned segment);
        @(posedge vif.CLK)
        disable iff(RESET || START)
        (vif.RDY && vif.ENA[segment]) |-> !$isunknown(vif.DATA[128*(segment+1)-1 -: 128]);
    endproperty

    // SOP must be always valid if the ENA is valid
    property valid_sop (int unsigned segment);
        @(posedge vif.CLK)
        disable iff(RESET || START)
        (vif.RDY && vif.ENA[segment]) |-> !$isunknown(vif.SOP[segment]);
    endproperty

    // EOP must be always valid if the ENA is valid
    property valid_eop (int unsigned segment);
        @(posedge vif.CLK)
        disable iff(RESET || START)
        (vif.RDY && vif.ENA[segment]) |-> !$isunknown(vif.EOP[segment]);
    endproperty

    // ERR must be always valid if the EOP is valid
    property valid_err (int unsigned segment);
        @(posedge vif.CLK)
        disable iff(RESET || START)
        (vif.RDY && vif.ENA[segment] && vif.EOP[segment]) |-> !$isunknown(vif.ERR[segment]);
    endproperty

    // MTY must be always valid if the EOP is valid
    property valid_mty (int unsigned segment);
        @(posedge vif.CLK)
        disable iff(RESET || START)
        (vif.RDY && vif.ENA[segment] && vif.EOP[segment]) |-> !$isunknown(vif.MTY[4*(segment+1)-1 -: 4]);
    endproperty

    // --------------------- //
    // Protocol restrictions //
    // --------------------- //

    // Gaps between valid segments are prohibited
    property no_gaps (int unsigned segment);
        @(posedge vif.CLK)
        disable iff(RESET || START)
        vif.RDY |-> (vif.ENA[segment] |-> vif.ENA[segment-1]);
    endproperty

    // It is forbidden to have multiple SOPs during one transaction
    property no_multiple_sops;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        vif.RDY |-> $onehot0(vif.ENA & vif.SOP);
    endproperty

    // It is forbidden to have multiple EOPs during one transaction
    property no_multiple_eops;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        vif.RDY |-> $onehot0(vif.ENA & vif.EOP);
    endproperty

    // ========== //
    // Assertions //
    // ========== //

    assert property (valid_rdy)
    else begin
        `uvm_error(module_name, "\n\tLBUS Interface: RDY must be always valid if the RESET is not set");
    end
    assert property (valid_ena)
    else begin
        `uvm_error(module_name, "\n\tLBUS Interface: ENA must be always valid if the RDY is set");
    end

    generate;
        for (genvar i = 0; i < 4; i++) begin
            assert property (valid_data(i))
            else begin
                `uvm_error(module_name, $sformatf("\n\tLBUS Interface: Segment %0d: DATA must be always valid if the ENA is valid", i));
            end
            assert property (valid_sop(i))
            else begin
                `uvm_error(module_name, $sformatf("\n\tLBUS Interface: Segment %0d: SOP must be always valid if the ENA is valid", i));
            end
            assert property (valid_eop(i))
            else begin
                `uvm_error(module_name, $sformatf("\n\tLBUS Interface: Segment %0d: EOP must be always valid if the ENA is valid", i));
            end
            assert property (valid_err(i))
            else begin
                `uvm_error(module_name, $sformatf("\n\tLBUS Interface: Segment %0d: ERR must be always valid if the EOP is valid", i));
            end
            assert property (valid_mty(i))
            else begin
                `uvm_error(module_name, $sformatf("\n\tLBUS Interface: Segment %0d: MTY must be always valid if the EOP is valid", i));
            end
        end

        for (genvar i = 1; i < 4; i++) begin
            assert property (no_gaps(i))
            else begin
                `uvm_error(module_name, $sformatf("\n\tLBUS Interface: Segment %0d: Gaps between valid segments are prohibited", i));
            end
        end
    endgenerate

    assert property (no_multiple_sops)
    else begin
        `uvm_error(module_name, "\n\tLBUS Interface: It is forbidden to have multiple SOPs during one transaction");
    end
    assert property (no_multiple_eops)
    else begin
        `uvm_error(module_name, "\n\tLBUS Interface: It is forbidden to have multiple EOPs during one transaction");
    end

endmodule
