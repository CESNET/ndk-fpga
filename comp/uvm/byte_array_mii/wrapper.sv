/*
 * file       : wrapper.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM Component, which converts simple byte_array to byte_array
 *              with standart MII preable and end of frame delimiter + control signals
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class wrapper extends uvm_object;
    `uvm_object_utils(uvm_byte_array_mii::wrapper)


    local const byte unsigned preamble[8] = {8'hFB, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'hD5};
    local const int unsigned preamble_size = 8 - 1;

    local const byte unsigned eof = 8'hFD;

    function new(string name = "wrapper");
        super.new(name);
    endfunction

    // Adds START character, preamble to beginning of of data and appends
    // END_OF_FRAME to end of data
    function void wrap_data(ref byte unsigned data[$], ref logic control[$]);
        control.push_back(1'b1);
        for (int i = 0; i < preamble_size + data.size(); i++) begin
            control.push_back(1'b0);
        end
        control.push_back(1'b1);

        for (int i = 7; i >= 0; i--) begin
            data.push_front(preamble[i]);
        end
        data.push_back(eof);
    endfunction

endclass
