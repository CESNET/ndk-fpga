/*
 * file       : channel_align.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM Object, which guarantees that next start of frame will be
 *              aligned to first byte of channel (does not matter which) by filling
 *              unused bytes of last block by IDLEs
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class channel_align #(int unsigned CHANNEL_WIDTH) extends uvm_object;

    `uvm_object_param_utils(uvm_byte_array_mii::channel_align #(CHANNEL_WIDTH))

    localparam BYTES = CHANNEL_WIDTH >> 3;

    function new(string name = "channel_align");
        super.new(name);

        WHOLE_BYTES : assert((CHANNEL_WIDTH & 7) == 0);
    endfunction

    // Appends IDLE characters to end of data to make sure next frame
    // starts at first byte of next channel
    function void align(ref byte unsigned data[$], ref logic control[$]);
        int unsigned bytes_remaining = data.size() % BYTES;
        int unsigned bytes_to_fill = BYTES - bytes_remaining;

        for (int i = 0; i < bytes_to_fill; i++) begin
            data.push_back(8'h07);
            control.push_back(1'b1);
        end
    endfunction

endclass
