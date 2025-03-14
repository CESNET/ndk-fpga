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

    function new (string file_name, string dev_tree[], string author = "anonymous", string revision = "0", string card_name = "NFB-VERIFICATION");
        int dt;
        string dtb_cmd;

        dt = $fopen({file_name, ".dts"}, "w");
        if(dt == 0) `uvm_fatal(`__FILE__, $sformatf("\n\tDevTree Cannot open file : %s for reading\n", {file_name, ".dts"}));
        $fwrite(dt, "/dts-v1/;\n\n");
        $fwrite(dt, "/ {\n\n");
        $fwrite(dt, "  firmware {\n");
        $fwrite(dt, "    build-tool = \"ModelSim\";\n");
        $fwrite(dt, "    build-author = \"%s\";\n", author);
        $fwrite(dt, "    build-revision = \"%s\";\n", revision);
        $fwrite(dt, "    build-time = <0x0>;\n");
        $fwrite(dt, "    card-name = \"%s\";\n\n", card_name);
        for (int unsigned it = 0; it < dev_tree.size(); it++) begin
            $fwrite(dt, "    mi%0d: mi_bus_%0d {\n", it, it);
            $fwrite(dt, "      compatible = \"netcope,bus,mi\";\n");
            $fwrite(dt, "      resource = \"PCI0,BAR0\";\n");
            $fwrite(dt, "      width = <0x20>;\n");
            $fwrite(dt, "      #address-cells = <1>;\n");
            $fwrite(dt, "      #size-cells = <1>;\n\n");
            $fwrite(dt, dev_tree[it]);
        end
        $fwrite(dt, "\n    };\n  };\n};\n");
        $fclose(dt);

        dtb_cmd = {"dtc -I dts -O dtb -o ", file_name, ".dtb ", file_name, ".dts"};
        if($system(dtb_cmd) != 0) `uvm_fatal(`__FILE__, $sformatf("\n\tDevTree cannot generate dtb file\n\t%s", dtb_cmd));

        dt = $fopen({file_name, ".dtb"}, "r");
        if (dt == 0) `uvm_fatal(`__FILE__, $sformatf("\n\tDevTree Cannot open file : %s for writing\n", {file_name, ".dts"}));
        $fread(data, dt);
        $fclose(dt);
    endfunction


    static function string read_dev_tree(string file_name);
        int dt;
        string ret;

        dt = $fopen(file_name, "r");
        if (dt == 0) `uvm_fatal(`__FILE__, $sformatf("\n\tDevTree Cannot open file : %s\n", file_name));
        $fread(ret, dt);
        $fclose(dt);

        return ret;
    endfunction

endclass

