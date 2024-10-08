/*
 * dma_bus_pack.sv: Package with DMA bus constatns
 * Copyright (C) 2019 CESNET
 * Author: Martin Spinler <spinler@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package sv_dma_bus_pack;

    // import math_pkg::*;//log2, max

    /* For item description see dma_bus_pack.vhd */
    /* Synchronize with dma_bus_pack.vhd! */

    parameter DMA_REQUEST_LENGTH_W          = 11;
    parameter DMA_REQUEST_TYPE_W            = 1;
    parameter DMA_REQUEST_FIRSTIB_W         = 2;
    parameter DMA_REQUEST_LASTIB_W          = 2;
    parameter DMA_REQUEST_TAG_W             = 8;
    parameter DMA_REQUEST_UNITID_W          = 8;
    parameter DMA_REQUEST_GLOBAL_W          = 64;
    parameter DMA_REQUEST_VFID_W            = 8;
    parameter DMA_REQUEST_PASID_W           = 0;
    parameter DMA_REQUEST_PASIDVLD_W        = 0;
    parameter DMA_REQUEST_RELAXED_W         = 1;

    parameter DMA_COMPLETION_LENGTH_W       = 11;
    parameter DMA_COMPLETION_COMPLETED_W    = 1;
    parameter DMA_COMPLETION_TAG_W          = 8;
    parameter DMA_COMPLETION_UNITID_W       = 8;

    parameter DMA_REQUEST_LENGTH_O          = 0;
    parameter DMA_REQUEST_TYPE_O            = DMA_REQUEST_LENGTH_O          + DMA_REQUEST_LENGTH_W;
    parameter DMA_REQUEST_FIRSTIB_O         = DMA_REQUEST_TYPE_O            + DMA_REQUEST_TYPE_W;
    parameter DMA_REQUEST_LASTIB_O          = DMA_REQUEST_FIRSTIB_O         + DMA_REQUEST_FIRSTIB_W;
    parameter DMA_REQUEST_TAG_O             = DMA_REQUEST_LASTIB_O          + DMA_REQUEST_LASTIB_W;
    parameter DMA_REQUEST_UNITID_O          = DMA_REQUEST_TAG_O             + DMA_REQUEST_TAG_W;
    parameter DMA_REQUEST_GLOBAL_O          = DMA_REQUEST_UNITID_O          + DMA_REQUEST_UNITID_W;
    parameter DMA_REQUEST_VFID_O            = DMA_REQUEST_GLOBAL_O          + DMA_REQUEST_GLOBAL_W;
    parameter DMA_REQUEST_PASID_O           = DMA_REQUEST_VFID_O            + DMA_REQUEST_VFID_W;
    parameter DMA_REQUEST_PASIDVLD_O        = DMA_REQUEST_PASID_O           + DMA_REQUEST_PASID_W;
    parameter DMA_REQUEST_RELAXED_O         = DMA_REQUEST_PASIDVLD_O        + DMA_REQUEST_PASIDVLD_W;

    parameter DMA_COMPLETION_LENGTH_O       = 0;
    parameter DMA_COMPLETION_COMPLETED_O    = DMA_COMPLETION_LENGTH_O       + DMA_COMPLETION_LENGTH_W;
    parameter DMA_COMPLETION_TAG_O          = DMA_COMPLETION_COMPLETED_O    + DMA_COMPLETION_COMPLETED_W;
    parameter DMA_COMPLETION_UNITID_O       = DMA_COMPLETION_TAG_O          + DMA_COMPLETION_TAG_W;

    parameter DMA_REQUEST_W                 = DMA_REQUEST_RELAXED_O         + DMA_REQUEST_RELAXED_W;
    parameter DMA_COMPLETION_W              = DMA_COMPLETION_UNITID_O       + DMA_COMPLETION_UNITID_W;

    parameter DMA_REQUEST_TYPE_WRITE        = 1;
    parameter DMA_REQUEST_TYPE_READ         = 0;

    /* For compatibility */
    parameter DMA_UPHDR_WIDTH               = DMA_REQUEST_W;
    parameter DMA_DOWNHDR_WIDTH             = DMA_COMPLETION_W;

    // Byte Enable conversion functions
    function logic[2-1 : 0] encode_fbe(logic [4-1 : 0] be, logic one_dw = 0);
        logic[2-1 : 0] ret;
        if (one_dw) begin
            casex (be)
                4'b1xx1 : ret = 2'b00;
                4'b01x1 : ret = 2'b01;
                4'b1x10 : ret = 2'b01;
                4'b0011 : ret = 2'b10;
                4'b0110 : ret = 2'b10;
                4'b1100 : ret = 2'b10;
                4'b0001 : ret = 2'b11;
                4'b0010 : ret = 2'b11;
                4'b0100 : ret = 2'b11;
                4'b1000 : ret = 2'b11;
                4'b0000 : ret = 2'b11;
            endcase
        end else begin
            casex (be)
                4'b0000 : ret = 2'b00;
                4'bxxx1 : ret = 2'b00;
                4'bxx10 : ret = 2'b01;
                4'bx100 : ret = 2'b10;
                4'b1000 : ret = 2'b11;
            endcase
        end
        return ret;
    endfunction

    function logic[2-1 : 0] encode_lbe(logic [4-1 : 0] be);
        logic[2-1 : 0] ret;
        casex (be)
            4'b0000 : ret = 2'b00;
            4'b1xxx : ret = 2'b00;
            4'b01xx : ret = 2'b01;
            4'b001x : ret = 2'b10;
            4'b0001 : ret = 2'b11;
        endcase
        return ret;
    endfunction

    function logic[4-1 : 0] decode_lbe(logic [1 : 0] ib);
        logic[4-1 : 0] be;
        case (ib)
            2'b00 : be = 4'b1111;
            2'b01 : be = 4'b0111;
            2'b10 : be = 4'b0011;
            2'b11 : be = 4'b0001;
        endcase

        return be;
    endfunction

    function logic[4-1 : 0] decode_fbe(logic [1 : 0] ib);
        logic[4-1 : 0] be;
        case (ib)
            2'b00 : be = 4'b1111;
            2'b01 : be = 4'b1110;
            2'b10 : be = 4'b1100;
            2'b11 : be = 4'b1000;
        endcase

        return be;
    endfunction

endpackage
