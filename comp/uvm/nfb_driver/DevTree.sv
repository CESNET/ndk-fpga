/*
 * file       : DevTree.sv
 * Copyright (C) 2025 CESNET z. s. p. o.
 * description: class representing device tree
 * date       : 2025
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class dev_tree;

    /*const*/ byte unsigned data[];

    function new (string file_name);
        int dt;

        dt = $fopen(file_name, "r");
        if (dt == 0) `uvm_fatal(`__FILE__, $sformatf("\n\tDevTree Cannot open file : %s for writing\n", file_name));
        $fread(data, dt);
        $fclose(dt);
    endfunction
endclass

