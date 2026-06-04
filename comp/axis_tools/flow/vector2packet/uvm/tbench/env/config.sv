// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>
// SPDX-License-Identifier: BSD-3-Clause

class config_sequence extends uvm_object;
    `ndk_object_utils(uvm_vector2packet::config_sequence)

    int unsigned space_size_min     = 0;
    int unsigned space_size_max     = 200;

    int unsigned frame_size_min     = 1;
    int unsigned frame_size_max     = 1500;

    int unsigned rdy_probability_min = 10;
    int unsigned rdy_probability_max = 100;


    function new(string name = "uvm_vector2packet::config_sequence");
        super.new(name);
    endfunction
endclass
