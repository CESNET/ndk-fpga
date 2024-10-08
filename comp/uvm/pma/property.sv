/*
 * file       : property.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: MII properties for assertion.
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

module pma_property #(int unsigned DATA_WIDTH) (
    input RESET,
    pma_if vif
);

    // -----------------------
    // Properties.
    // -----------------------

    // This property check if after HDR_VLD is valid value of HDR.
    property valid_hdr_values;
        @(posedge vif.CLK)
        disable iff(RESET == 1'b1 || vif.DATA_VLD == 1'b0)
        (vif.HDR_VLD == 1'b1) |-> (vif.HDR == 2'b01 || vif.HDR == 2'b10);
    endproperty

    // This property check if next cycle after HDR_VLD is not another HDR_VLD.
    property valid_header_once_per_two_clk_cycles;
        @(posedge vif.CLK)
        disable iff(RESET == 1'b1 || vif.DATA_VLD == 1'b0)
        ((vif.HDR_VLD == 1'b1 && vif.DATA_VLD == 1'b1) |=> (vif.HDR_VLD == 1'b0 && vif.DATA_VLD == 1'b1));
    endproperty

    // -----------------------
    // Assertion.
    // -----------------------

    assert property (valid_hdr_values)
        else begin
            $error("When HDR_VLD occured 'h%0b, HDR has not valid value : 'h%0h", vif.HDR_VLD, vif.HDR);
            $finish();
        end
    assert property (valid_header_once_per_two_clk_cycles)
        else begin
            $error("After HDR_VLD 'h%0b another HDR_VLD occured : 'h%0h", $past(vif.HDR_VLD), vif.HDR_VLD);
            $finish();
        end

endmodule
