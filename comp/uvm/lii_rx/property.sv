/*
 * file       : property.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: LII properties for assertion.
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

module lii_property_rx #(logic FAST_SOF, logic RESET_ENABLE, int unsigned DATA_WIDTH)
    (
        input RESET,
        lii_if_rx vif
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

    // This property check if after SOF is EOF.
    property sof_eof_control;
	    @(posedge vif.CLK)
        disable iff(RESET == 1'b1)
            (vif.SOF) && (!vif.EOF) && (vif.RDY) |=>
            !((vif.SOF && !vif.EOF) || (vif.SOF && vif.EOF) && (vif.RDY)) throughout eof_seq;
    endproperty

    property error_check;
        bit inframe;
        @(posedge vif.CLK)
        disable iff(RESET == 1'b1 || vif.LINK_STATUS == 1'b0)
            (vif.RXSEQERR || vif.RXBLKERR || vif.RXIDLE || vif.RXRMTERR || vif.RXLOCERR) |-> vif.ERR  throughout sof_seq
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
