-- axis_eth_parser_types.vhd: Type definitions for AXI-Stream Ethernet Parser
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- This package defines the protocol identifiers, the header record types and
-- the functions that describe each protocol. All protocol-specific logic of
-- the parser is in this package.
--
-- Header data from a parser stage stores byte 0 of the header in bits 7:0.
--
package axis_eth_parser_types is

    -- =========================================================================
    -- Protocol identifiers
    -- =========================================================================
    constant PROTO_NONE    : natural := 0;  -- No valid protocol
    constant PROTO_ETH     : natural := 1;  -- Ethernet header
    constant PROTO_VLAN    : natural := 2;  -- VLAN tag
    constant PROTO_IPV4    : natural := 3;  -- IPv4 header
    constant PROTO_TCP     : natural := 4;  -- TCP header
    constant PROTO_UDP     : natural := 5;  -- UDP header
    constant PROTO_IPV6    : natural := 6;  -- IPv6 header
    constant PROTO_IPV6EXT : natural := 7;  -- IPv6 extension header
    constant PROTO_MPLS    : natural := 8;  -- MPLS label stack entry

    -- Width of protocol identifier field (must accommodate all PROTO_* values)
    constant PROTOCOL_WIDTH : natural := 4;

    -- Protocols of the parser stages in pipeline order
    type proto_array_t is array (natural range <>) of natural;

    -- Maximum number of parser stages, given by the width of the STAGE_REG bitmap
    constant MAX_STAGES : natural := 64;

    -- Maximum width of offset field (supports PKT_MTU up to 2^14)
    -- This is the maximum offset width used in extracted_headers_t record
    constant MAX_OFFSET_WIDTH : natural := 15;

    -- Ethernet MAC address size in bytes
    constant ETH_MAC_SIZE : natural := 6;

    -- =========================================================================
    -- Header record types
    -- =========================================================================

    -- Ethernet header fields
    type eth_header_t is record
        dst_mac   : std_logic_vector(ETH_MAC_SIZE*8-1 downto 0);  -- Destination MAC address
        src_mac   : std_logic_vector(ETH_MAC_SIZE*8-1 downto 0);  -- Source MAC address
        ethertype : std_logic_vector(15 downto 0);                -- Ethertype/length field
    end record;

    -- VLAN tag fields
    type vlan_header_t is record
        tci       : std_logic_vector(15 downto 0);  -- Tag Control Information: PCP(3) + DEI(1) + VID(12)
        ethertype : std_logic_vector(15 downto 0);  -- Encapsulated protocol ethertype
    end record;

    -- IPv4 header fields
    type ipv4_header_t is record
        version         : std_logic_vector(3 downto 0);   -- IP version (4 for IPv4)
        ihl             : std_logic_vector(3 downto 0);   -- Internet Header Length (in 32-bit words)
        tos             : std_logic_vector(7 downto 0);   -- Type of Service
        total_length    : std_logic_vector(15 downto 0);  -- Total packet length
        identification  : std_logic_vector(15 downto 0);  -- Packet identification
        flags           : std_logic_vector(2 downto 0);   -- Fragmentation flags
        fragment_offset : std_logic_vector(12 downto 0);  -- Fragment offset
        ttl             : std_logic_vector(7 downto 0);   -- Time to Live
        protocol        : std_logic_vector(7 downto 0);   -- Upper layer protocol
        header_checksum : std_logic_vector(15 downto 0);  -- Header checksum
        src_ip          : std_logic_vector(31 downto 0);  -- Source IP address
        dst_ip          : std_logic_vector(31 downto 0);  -- Destination IP address
    end record;

    -- TCP header fields
    type tcp_header_t is record
        src_port    : std_logic_vector(15 downto 0);  -- Source port
        dst_port    : std_logic_vector(15 downto 0);  -- Destination port
        seq_num     : std_logic_vector(31 downto 0);  -- Sequence number
        ack_num     : std_logic_vector(31 downto 0);  -- Acknowledgment number
        data_offset : std_logic_vector(3 downto 0);   -- Data offset (header length in 32-bit words)
        reserved    : std_logic_vector(2 downto 0);   -- Reserved bits
        flags       : std_logic_vector(8 downto 0);   -- Control flags (NS, CWR, ECE, URG, ACK, PSH, RST, SYN, FIN)
        window      : std_logic_vector(15 downto 0);  -- Receive window size
        checksum    : std_logic_vector(15 downto 0);  -- Checksum
        urgent_ptr  : std_logic_vector(15 downto 0);  -- Urgent pointer
    end record;

    -- UDP header fields
    type udp_header_t is record
        src_port : std_logic_vector(15 downto 0);  -- Source port
        dst_port : std_logic_vector(15 downto 0);  -- Destination port
        length   : std_logic_vector(15 downto 0);  -- UDP length (header + data)
        checksum : std_logic_vector(15 downto 0);  -- UDP checksum
    end record;

    -- IPv6 header fields
    type ipv6_header_t is record
        version        : std_logic_vector(3 downto 0);    -- IP version (6 for IPv6)
        traffic_class  : std_logic_vector(7 downto 0);    -- Traffic class
        flow_label     : std_logic_vector(19 downto 0);   -- Flow label
        payload_length : std_logic_vector(15 downto 0);   -- Length of the data after this header
        next_header    : std_logic_vector(7 downto 0);    -- Type of the next header
        hop_limit      : std_logic_vector(7 downto 0);    -- Hop limit
        src_ip         : std_logic_vector(127 downto 0);  -- Source IP address
        dst_ip         : std_logic_vector(127 downto 0);  -- Destination IP address
    end record;

    -- IPv6 extension header fields (Hop-by-Hop, Routing, Fragment, Destination Options)
    type ipv6ext_header_t is record
        next_header : std_logic_vector(7 downto 0);   -- Type of the next header
        hdr_ext_len : std_logic_vector(7 downto 0);   -- Header length in 8-byte units, without the first 8 bytes
        data        : std_logic_vector(47 downto 0);  -- Bytes 2 to 7 of the header
    end record;

    -- MPLS label stack entry fields
    type mpls_header_t is record
        label_value : std_logic_vector(19 downto 0);  -- Label value
        tc          : std_logic_vector(2 downto 0);   -- Traffic class
        s           : std_logic;                      -- Bottom of stack flag
        ttl         : std_logic_vector(7 downto 0);   -- Time to Live
    end record;

    -- Headers of the AXIS_ETH_PARSER protocol set
    -- Uses MAX_OFFSET_WIDTH to support any PKT_MTU up to 2^14 bytes
    type extracted_headers_t is record
        eth         : eth_header_t;
        eth_vld     : std_logic;
        eth_offset  : unsigned(MAX_OFFSET_WIDTH-1 downto 0);
        vlan        : vlan_header_t;
        vlan_vld    : std_logic;
        vlan_offset : unsigned(MAX_OFFSET_WIDTH-1 downto 0);
        ipv4        : ipv4_header_t;
        ipv4_vld    : std_logic;
        ipv4_offset : unsigned(MAX_OFFSET_WIDTH-1 downto 0);
        tcp         : tcp_header_t;
        tcp_vld     : std_logic;
        tcp_offset  : unsigned(MAX_OFFSET_WIDTH-1 downto 0);
        udp         : udp_header_t;
        udp_vld     : std_logic;
        udp_offset  : unsigned(MAX_OFFSET_WIDTH-1 downto 0);
    end record;

    -- =========================================================================
    -- Protocol description
    -- =========================================================================

    -- Number of header bytes that a stage reads for the protocol.
    -- It must not be larger than the minimum header length plus one.
    -- The next stage then gets its start no later than the AXI word that contains its header.
    function get_extract_bytes (protocol : natural) return natural;
    function get_max_extract_bytes (protocols : proto_array_t) return natural;

    -- Header length in bytes, data contains the bytes read by the stage
    function get_hdr_len (protocol : natural; data : std_logic_vector) return natural;
    -- Protocol of the next header, data contains the bytes read by the stage
    function get_next_proto (protocol : natural; data : std_logic_vector) return natural;

    -- True when a header of protocol next_proto can directly follow a header of protocol proto
    function proto_can_follow (proto : natural; next_proto : natural) return boolean;
    -- Index of the inst-th stage with the protocol, the first stage has index 0
    function get_stage_index (protocols : proto_array_t; protocol : natural; inst : natural := 0) return natural;
    -- Bit i is set when a register stage after stage i is needed for timing.
    -- It is needed after a stage that computes a variable header length (IPv4, IPv6 extension header).
    function get_stage_reg_auto (protocols : proto_array_t) return std_logic_vector;

    -- =========================================================================
    -- Header decoding
    -- =========================================================================

    -- Bytes first to first+bytes-1 of data in network byte order (byte first in the MSBs)
    function get_be (data : std_logic_vector; first : natural; bytes : natural) return std_logic_vector;

    function decode_eth (data : std_logic_vector) return eth_header_t;
    function decode_vlan (data : std_logic_vector) return vlan_header_t;
    function decode_ipv4 (data : std_logic_vector) return ipv4_header_t;
    function decode_tcp (data : std_logic_vector) return tcp_header_t;
    function decode_udp (data : std_logic_vector) return udp_header_t;
    function decode_ipv6 (data : std_logic_vector) return ipv6_header_t;
    function decode_ipv6ext (data : std_logic_vector) return ipv6ext_header_t;
    function decode_mpls (data : std_logic_vector) return mpls_header_t;

end package;

package body axis_eth_parser_types is

    function get_extract_bytes (protocol : natural) return natural is
    begin
        case protocol is
            when PROTO_ETH     => return 14;
            when PROTO_VLAN    => return 4;
            when PROTO_IPV4    => return 20;
            when PROTO_TCP     => return 20;
            when PROTO_UDP     => return 8;
            when PROTO_IPV6    => return 40;
            when PROTO_IPV6EXT => return 8;
            -- The fifth byte is the first byte after the label stack entry
            when PROTO_MPLS    => return 5;
            when others =>
                report "AXIS_ETH_PARSER: Use only the PROTO_* constants that this package defines."
                    severity failure;
                return 1;
        end case;
    end function;

    function get_max_extract_bytes (protocols : proto_array_t) return natural is
        variable r : natural := 1;
    begin
        for i in protocols'range loop
            r := maximum(r, get_extract_bytes(protocols(i)));
        end loop;
        return r;
    end function;

    function get_be (data : std_logic_vector; first : natural; bytes : natural) return std_logic_vector is
        alias    d : std_logic_vector(data'length-1 downto 0) is data;
        variable r : std_logic_vector(bytes*8-1 downto 0);
    begin
        for i in 0 to bytes-1 loop
            r((bytes-i)*8-1 downto (bytes-i-1)*8) := d((first+i)*8+7 downto (first+i)*8);
        end loop;
        return r;
    end function;

    function ethertype_to_proto (ethertype : std_logic_vector(15 downto 0)) return natural is
    begin
        case ethertype is
            when X"8100" | X"88A8" | X"9100" => return PROTO_VLAN;
            when X"0800" => return PROTO_IPV4;
            when X"86DD" => return PROTO_IPV6;
            when X"8847" | X"8848" => return PROTO_MPLS;
            when others  => return PROTO_NONE;
        end case;
    end function;

    function get_hdr_len (protocol : natural; data : std_logic_vector) return natural is
        variable b0  : std_logic_vector(7 downto 0);
        variable ihl : natural;
    begin
        case protocol is
            when PROTO_IPV4 =>
                b0  := get_be(data, 0, 1);
                ihl := to_integer(unsigned(b0(3 downto 0)));
                -- IHL below 5 is not valid. The minimum header length is used instead.
                if (ihl < 5) then
                    return 20;
                end if;
                return ihl * 4;
            when PROTO_MPLS =>
                return 4;
            when PROTO_IPV6EXT =>
                -- Byte 1 of the Fragment header is reserved and zero. The formula then gives its length of 8 bytes.
                return (to_integer(unsigned(get_be(data, 1, 1))) + 1) * 8;
            when others =>
                return get_extract_bytes(protocol);
        end case;
    end function;

    function ip_proto_to_proto (ip_proto : std_logic_vector(7 downto 0)) return natural is
    begin
        case ip_proto is
            when X"06"  => return PROTO_TCP;
            when X"11"  => return PROTO_UDP;
            when others => return PROTO_NONE;
        end case;
    end function;

    function ipv6_next_to_proto (next_header : std_logic_vector(7 downto 0)) return natural is
    begin
        case next_header is
            when X"00" | X"2B" | X"2C" | X"3C" => return PROTO_IPV6EXT;
            when others => return ip_proto_to_proto(next_header);
        end case;
    end function;

    function get_next_proto (protocol : natural; data : std_logic_vector) return natural is
        variable b2 : std_logic_vector(7 downto 0);
        variable b4 : std_logic_vector(7 downto 0);
    begin
        case protocol is
            when PROTO_ETH =>
                return ethertype_to_proto(get_be(data, 12, 2));
            when PROTO_VLAN =>
                return ethertype_to_proto(get_be(data, 2, 2));
            when PROTO_IPV4 =>
                return ip_proto_to_proto(get_be(data, 9, 1));
            when PROTO_IPV6 =>
                return ipv6_next_to_proto(get_be(data, 6, 1));
            when PROTO_IPV6EXT =>
                return ipv6_next_to_proto(get_be(data, 0, 1));
            when PROTO_MPLS =>
                b2 := get_be(data, 2, 1);
                b4 := get_be(data, 4, 1);
                if (b2(0) = '0') then
                    return PROTO_MPLS;
                end if;
                -- The label stack does not announce the payload protocol. The IP version field selects it instead.
                case b4(7 downto 4) is
                    when X"4"   => return PROTO_IPV4;
                    when X"6"   => return PROTO_IPV6;
                    when others => return PROTO_NONE;
                end case;
            when others =>
                return PROTO_NONE;
        end case;
    end function;

    function proto_can_follow (proto : natural; next_proto : natural) return boolean is
    begin
        case proto is
            when PROTO_ETH | PROTO_VLAN =>
                return (next_proto = PROTO_VLAN) or (next_proto = PROTO_MPLS) or
                       (next_proto = PROTO_IPV4) or (next_proto = PROTO_IPV6);
            when PROTO_MPLS =>
                return (next_proto = PROTO_MPLS) or (next_proto = PROTO_IPV4) or (next_proto = PROTO_IPV6);
            when PROTO_IPV4 =>
                return (next_proto = PROTO_TCP) or (next_proto = PROTO_UDP);
            when PROTO_IPV6 | PROTO_IPV6EXT =>
                return (next_proto = PROTO_TCP) or (next_proto = PROTO_UDP) or (next_proto = PROTO_IPV6EXT);
            when others =>
                return false;
        end case;
    end function;

    function get_stage_index (protocols : proto_array_t; protocol : natural; inst : natural := 0) return natural is
        variable cnt : natural := 0;
    begin
        for i in 0 to protocols'length-1 loop
            if (protocols(protocols'low + i) = protocol) then
                if (cnt = inst) then
                    return i;
                end if;
                cnt := cnt + 1;
            end if;
        end loop;
        report "AXIS_ETH_PARSER: The protocol list does not contain the requested stage."
            severity failure;
        return 0;
    end function;

    function get_stage_reg_auto (protocols : proto_array_t) return std_logic_vector is
        variable r : std_logic_vector(MAX_STAGES-1 downto 0) := (others => '0');
    begin
        -- The output of the last stage is not connected to another stage
        for i in 0 to protocols'length-2 loop
            if ((protocols(protocols'low + i) = PROTO_IPV4) or (protocols(protocols'low + i) = PROTO_IPV6EXT)) then
                r(i) := '1';
            end if;
        end loop;
        return r;
    end function;

    function decode_eth (data : std_logic_vector) return eth_header_t is
        variable r : eth_header_t;
    begin
        r.dst_mac   := get_be(data, 0, 6);
        r.src_mac   := get_be(data, 6, 6);
        r.ethertype := get_be(data, 12, 2);
        return r;
    end function;

    function decode_vlan (data : std_logic_vector) return vlan_header_t is
        variable r : vlan_header_t;
    begin
        r.tci       := get_be(data, 0, 2);
        r.ethertype := get_be(data, 2, 2);
        return r;
    end function;

    function decode_ipv4 (data : std_logic_vector) return ipv4_header_t is
        variable r    : ipv4_header_t;
        variable b0   : std_logic_vector(7 downto 0);
        variable b6_7 : std_logic_vector(15 downto 0);
    begin
        b0                := get_be(data, 0, 1);
        b6_7              := get_be(data, 6, 2);
        r.version         := b0(7 downto 4);
        r.ihl             := b0(3 downto 0);
        r.tos             := get_be(data, 1, 1);
        r.total_length    := get_be(data, 2, 2);
        r.identification  := get_be(data, 4, 2);
        r.flags           := b6_7(15 downto 13);
        r.fragment_offset := b6_7(12 downto 0);
        r.ttl             := get_be(data, 8, 1);
        r.protocol        := get_be(data, 9, 1);
        r.header_checksum := get_be(data, 10, 2);
        r.src_ip          := get_be(data, 12, 4);
        r.dst_ip          := get_be(data, 16, 4);
        return r;
    end function;

    function decode_tcp (data : std_logic_vector) return tcp_header_t is
        variable r      : tcp_header_t;
        variable b12_13 : std_logic_vector(15 downto 0);
    begin
        b12_13        := get_be(data, 12, 2);
        r.src_port    := get_be(data, 0, 2);
        r.dst_port    := get_be(data, 2, 2);
        r.seq_num     := get_be(data, 4, 4);
        r.ack_num     := get_be(data, 8, 4);
        r.data_offset := b12_13(15 downto 12);
        r.reserved    := b12_13(11 downto 9);
        r.flags       := b12_13(8 downto 0);
        r.window      := get_be(data, 14, 2);
        r.checksum    := get_be(data, 16, 2);
        r.urgent_ptr  := get_be(data, 18, 2);
        return r;
    end function;

    function decode_udp (data : std_logic_vector) return udp_header_t is
        variable r : udp_header_t;
    begin
        r.src_port := get_be(data, 0, 2);
        r.dst_port := get_be(data, 2, 2);
        r.length   := get_be(data, 4, 2);
        r.checksum := get_be(data, 6, 2);
        return r;
    end function;

    function decode_ipv6 (data : std_logic_vector) return ipv6_header_t is
        variable r    : ipv6_header_t;
        variable b0_3 : std_logic_vector(31 downto 0);
    begin
        b0_3             := get_be(data, 0, 4);
        r.version        := b0_3(31 downto 28);
        r.traffic_class  := b0_3(27 downto 20);
        r.flow_label     := b0_3(19 downto 0);
        r.payload_length := get_be(data, 4, 2);
        r.next_header    := get_be(data, 6, 1);
        r.hop_limit      := get_be(data, 7, 1);
        r.src_ip         := get_be(data, 8, 16);
        r.dst_ip         := get_be(data, 24, 16);
        return r;
    end function;

    function decode_ipv6ext (data : std_logic_vector) return ipv6ext_header_t is
        variable r : ipv6ext_header_t;
    begin
        r.next_header := get_be(data, 0, 1);
        r.hdr_ext_len := get_be(data, 1, 1);
        r.data        := get_be(data, 2, 6);
        return r;
    end function;

    function decode_mpls (data : std_logic_vector) return mpls_header_t is
        variable r    : mpls_header_t;
        variable b0_3 : std_logic_vector(31 downto 0);
    begin
        b0_3          := get_be(data, 0, 4);
        r.label_value := b0_3(31 downto 12);
        r.tc          := b0_3(11 downto 9);
        r.s           := b0_3(8);
        r.ttl         := b0_3(7 downto 0);
        return r;
    end function;

end package body;
