/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

class tag_manager;
    string inst;
    int tags[int];
    int unsigned verbose = 0;

    function new(string inst);
        this.inst = inst;
    endfunction

    function void set(int unsigned tag);
        if (verbose > 1) begin
            $write("%s register tag %4d\n", inst, tag);
        end

        if (tags.exists(tag) == 1) begin
            $error("%s tag %4d already used and have not been compleated!\n", inst, tag);
            $stop();
        end
        tags[tag] = 1;
    endfunction

    function void remove(int unsigned tag);
        if (verbose > 1) begin
            $write("%s compleated tag %4d\n", inst, tag);
        end
        tags.delete(tag);
    endfunction
endclass


