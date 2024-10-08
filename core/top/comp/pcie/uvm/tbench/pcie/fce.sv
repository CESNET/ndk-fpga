// fce.sv: pcie function to simplify manipulation 
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


function int unsigned encode_fbe(logic [32/8-1 : 0] be);
    automatic int unsigned it = 0;

    if (be != 0) begin
        while (it < 32/8 && be[it] == 0) begin
            it++;
        end
    end
    return it;
endfunction

function int unsigned encode_lbe(logic [32/8-1 : 0] be);
     automatic int unsigned it  = 32/8;

    if (be != 0) begin
        while (it > 0 && be[it-1] == 0) begin
            it--;
        end;
    end
    return it;
endfunction





