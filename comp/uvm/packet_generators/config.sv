// config.sv: Configuration for sequence library
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class config_sequence extends uvm_logic_vector_array::config_sequence;
    logic [31 : 0]  ipv4_addresses [$];
    logic [127 : 0] ipv6_addresses [$];

    function void add_ipv4_address(logic [31 : 0] ipv4_address);
        ipv4_addresses.push_back(ipv4_address);
    endfunction

    function void add_ipv6_address(logic [127 : 0] ipv6_address);
        ipv6_addresses.push_back(ipv6_address);
    endfunction

endclass
