// config.sv: Configuration for sequence library
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class config_sequence extends uvm_logic_vector_array::config_sequence;
    bit [31 : 0]  ipv4_addresses [$];
    bit [127 : 0] ipv6_addresses [$];
    bit [47 : 0]  mac_addresses  [$];

    function void add_ipv4_address(bit [31 : 0] ipv4_address);
        ipv4_addresses.push_back(ipv4_address);
    endfunction

    function void add_ipv6_address(bit [127 : 0] ipv6_address);
        ipv6_addresses.push_back(ipv6_address);
    endfunction

    function void add_mac_address(bit [47 : 0] mac_address);
        mac_addresses.push_back(mac_address);
    endfunction

endclass
