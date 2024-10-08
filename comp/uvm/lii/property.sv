/*
 * file       : property.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: LII properties for assertion.
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

module lii_property #(logic FAST_SOF, logic RESET_ENABLE, int unsigned DATA_WIDTH)
    (
        input RESET,
        lii_if vif
    );

    localparam BYTES_VLD_LENGTH = $clog2(DATA_WIDTH/8)+1;

    // -----------------------
    // Properties.
    // -----------------------

    // Sequence which will start when EOF is asserted.
    sequence eof_seq;
        ##[0:$] (vif.EOF) && (vif.RDY);
    endsequence

    // Sequence which will start when SOF is asserted.
    sequence sof_seq;
        ##[0:$] (vif.SOF) && (vif.RDY);
    endsequence

    // This property check if EOF is asserted after EEOF
    property eof_after_eeof;
        @(posedge vif.CLK)
        disable iff(RESET == 1'b1)
        (vif.EEOF && vif.RDY) |=> vif.EOF;
    endproperty

    // This property check if after EEOF has BYTES_VLD same value as EDB in clock before.
    property byte_valid_control;
        logic [BYTES_VLD_LENGTH-1 : 0] edb;
        @(posedge vif.CLK)
        disable iff(RESET == 1'b1)
        ((vif.EEOF && vif.RDY), edb = vif.EDB) |->
        (vif.EEOF == 1'b1) |=> (edb == vif.BYTES_VLD);
    endproperty

    // This property check if after SOF is EOF.
    property sof_eof_control;
	    @(posedge vif.CLK)
        disable iff(RESET == 1'b1)
            (vif.SOF) && (!vif.EOF) && (vif.RDY) |=>
            !((vif.SOF && !vif.EOF) || (vif.SOF && vif.EOF) && (vif.RDY)) throughout eof_seq;
    endproperty

    // TODO: Repair property for TX MAC
    // This property check if after EOF is SOF
    //property no_data_after_eof;
	//    @(posedge vif.CLK)
    //    disable iff(RESET == 1'b1)
    //        (vif.EOF) && (!vif.SOF) && (vif.RDY) |=>
    //        !(!vif.SOF && vif.RDY) throughout sof_seq;
    //endproperty

    // -----------------------
    // Assertion.
    // -----------------------

    generate
        if (FAST_SOF == 1'b1) begin
            assert property (eof_after_eeof)
                else begin
                    $error("After EEOF 'h%0h is not EOF: 'h%0h", vif.EEOF, vif.EOF);
                    $finish();
                end

            assert property (byte_valid_control)
                else begin
                    $error("After EEOF: 'h%0h is not BYTES_VLD: 'h%0h equal to EDB: 'h%0h", $past(vif.EEOF), $past(vif.EDB), vif.BYTES_VLD);
                    $finish();
                end
        end
    endgenerate

    generate
        if (RESET_ENABLE == 1'b1) begin
            assert property (sof_eof_control)
                else begin
                    $error("After SOF is not EOF");
                    $finish();
                end

            //assert property (no_data_after_eof)
            //    else begin
            //        $error("Multiple EOFs in one high level transaction");
            //        $finish();
            //    end
        end
    endgenerate

endmodule
