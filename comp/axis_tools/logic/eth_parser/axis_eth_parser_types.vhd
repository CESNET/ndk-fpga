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

-- This package defines types and constants used throughout the AXI-Stream
-- Ethernet parser components. It includes protocol identifiers, header field
-- sizes, ethertype values for protocol detection, and record types for
-- representing parsed headers from each protocol layer.
--
package axis_eth_parser_types is

    -- =========================================================================
    -- Protocol identifiers
    -- =========================================================================
    constant PROTO_NONE   : natural := 0;  -- No valid protocol
    constant PROTO_ETH    : natural := 1;  -- Ethernet header
    constant PROTO_VLAN   : natural := 2;  -- VLAN tag
    constant PROTO_IPV4   : natural := 3;  -- IPv4 header
    constant PROTO_TCP    : natural := 4;  -- TCP header

    -- Width of protocol identifier field (must accommodate all PROTO_* values)
    constant PROTOCOL_WIDTH : natural := 3;

    -- Maximum width of offset field (supports PKT_MTU up to 2^14)
    -- This is the maximum offset width used in extracted_headers_t record
    constant MAX_OFFSET_WIDTH : natural := 15;

    -- =========================================================================
    -- Ethernet header constants
    -- =========================================================================
    constant ETH_HDR_SIZE      : natural := 14;  -- Total Ethernet header size: dst_mac(6) + src_mac(6) + ethertype(2)
    constant ETH_HDR_EXTRACT   : natural := 14;  -- Bytes to extract for Ethernet header
    constant ETH_MAC_SIZE      : natural := 6;   -- MAC address size in bytes
    constant ETH_ETHERTYPE_OFS : natural := 12;  -- Ethertype field offset

    -- Ethertype values for next protocol identification
    constant ETH_TYPE_IPV4 : std_logic_vector(15 downto 0) := X"0800";  -- IPv4
    constant ETH_TYPE_VLAN : std_logic_vector(15 downto 0) := X"8100";  -- VLAN tag

    -- =========================================================================
    -- VLAN header constants
    -- =========================================================================
    constant VLAN_HDR_SIZE    : natural := 4;   -- Total VLAN tag size: tpid(2) + tci(2)
    constant VLAN_HDR_EXTRACT : natural := 4;   -- Bytes to extract for VLAN header

    -- =========================================================================
    -- IPv4 header constants
    -- =========================================================================
    constant IPV4_HDR_MIN_SIZE : natural := 20;  -- Minimum IPv4 header size (IHL=5)
    constant IPV4_HDR_EXTRACT  : natural := 20;  -- Bytes to extract for IPv4 header

    -- IPv4 protocol field values
    constant IPV4_PROTO_TCP : std_logic_vector(7 downto 0) := X"06";  -- TCP

    -- =========================================================================
    -- TCP header constants
    -- =========================================================================
    constant TCP_HDR_MIN_SIZE : natural := 20;  -- Minimum TCP header size (data offset=5)
    constant TCP_HDR_EXTRACT  : natural := 20;  -- Bytes to extract for TCP header

    -- =========================================================================
    -- Function declarations
    -- =========================================================================
    function get_extract_bytes (protocol : natural) return natural;
    function get_max_extract_bytes return natural;

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

    -- Combined extracted headers from all protocol layers
    -- Uses MAX_OFFSET_WIDTH to support any PKT_MTU up to 2^16 bytes
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
    end record;

    -- =========================================================================
    -- Helper function declarations
    -- =========================================================================
    function init_extracted_headers return extracted_headers_t;
    function extracted_headers_to_slv (hdrs : extracted_headers_t; OFFSET_WIDTH : natural) return std_logic_vector;
    function slv_to_extracted_headers (slv : std_logic_vector; OFFSET_WIDTH : natural) return extracted_headers_t;

end package;

package body axis_eth_parser_types is

    -- Initialize all header fields to zero/invalid
    function init_extracted_headers return extracted_headers_t is
        variable r : extracted_headers_t;
    begin
        r.eth.dst_mac          := (others => '0');
        r.eth.src_mac          := (others => '0');
        r.eth.ethertype        := (others => '0');
        r.eth_vld              := '0';
        r.eth_offset           := (others => '0');
        r.vlan.tci             := (others => '0');
        r.vlan.ethertype       := (others => '0');
        r.vlan_vld             := '0';
        r.vlan_offset          := (others => '0');
        r.ipv4.version         := (others => '0');
        r.ipv4.ihl             := (others => '0');
        r.ipv4.tos             := (others => '0');
        r.ipv4.total_length    := (others => '0');
        r.ipv4.identification  := (others => '0');
        r.ipv4.flags           := (others => '0');
        r.ipv4.fragment_offset := (others => '0');
        r.ipv4.ttl             := (others => '0');
        r.ipv4.protocol        := (others => '0');
        r.ipv4.header_checksum := (others => '0');
        r.ipv4.src_ip          := (others => '0');
        r.ipv4.dst_ip          := (others => '0');
        r.ipv4_vld             := '0';
        r.ipv4_offset          := (others => '0');
        r.tcp.src_port         := (others => '0');
        r.tcp.dst_port         := (others => '0');
        r.tcp.seq_num          := (others => '0');
        r.tcp.ack_num          := (others => '0');
        r.tcp.data_offset      := (others => '0');
        r.tcp.reserved         := (others => '0');
        r.tcp.flags            := (others => '0');
        r.tcp.window           := (others => '0');
        r.tcp.checksum         := (others => '0');
        r.tcp.urgent_ptr       := (others => '0');
        r.tcp_vld              := '0';
        r.tcp_offset           := (others => '0');
        return r;
    end function;

    -- Return number of bytes to extract for given protocol
    function get_extract_bytes (protocol : natural) return natural is
    begin
        case protocol is
            when PROTO_ETH => return ETH_HDR_EXTRACT;
            when PROTO_VLAN => return VLAN_HDR_EXTRACT;
            when PROTO_IPV4 => return IPV4_HDR_EXTRACT;
            when PROTO_TCP => return TCP_HDR_EXTRACT;
            when others => return 20;
        end case;
    end function;

    -- Return maximum bytes required across all supported protocols
    function get_max_extract_bytes return natural is
    begin
        return maximum(maximum(maximum(ETH_HDR_EXTRACT, VLAN_HDR_EXTRACT), IPV4_HDR_EXTRACT), TCP_HDR_EXTRACT);
    end function;

    -- Convert extracted_headers_t record to std_logic_vector for serialization
    -- OFFSET_WIDTH specifies the actual width of offset fields to use (must be <= MAX_OFFSET_WIDTH)
    function extracted_headers_to_slv (hdrs : extracted_headers_t; OFFSET_WIDTH : natural) return std_logic_vector is
        variable r   : std_logic_vector(511 downto 0);
        variable pos : natural := 0;
    begin
        -- Ethernet: 48+48+16+1+OFFSET_WIDTH bits
        r(pos+47 downto pos)             := hdrs.eth.dst_mac;       pos := pos + 48;
        r(pos+47 downto pos)             := hdrs.eth.src_mac;       pos := pos + 48;
        r(pos+15 downto pos)             := hdrs.eth.ethertype;     pos := pos + 16;
        r(pos)                           := hdrs.eth_vld;           pos := pos + 1;
        r(pos+OFFSET_WIDTH-1 downto pos) := std_logic_vector(hdrs.eth_offset(OFFSET_WIDTH-1 downto 0)); pos := pos + OFFSET_WIDTH;
        -- VLAN: 16+16+1+OFFSET_WIDTH bits
        r(pos+15 downto pos)             := hdrs.vlan.tci;          pos := pos + 16;
        r(pos+15 downto pos)             := hdrs.vlan.ethertype;    pos := pos + 16;
        r(pos)                           := hdrs.vlan_vld;          pos := pos + 1;
        r(pos+OFFSET_WIDTH-1 downto pos) := std_logic_vector(hdrs.vlan_offset(OFFSET_WIDTH-1 downto 0)); pos := pos + OFFSET_WIDTH;
        -- IPv4: 4+4+8+16+16+3+13+8+8+16+32+32+1+OFFSET_WIDTH bits
        r(pos+3 downto pos)              := hdrs.ipv4.version;       pos := pos + 4;
        r(pos+3 downto pos)              := hdrs.ipv4.ihl;           pos := pos + 4;
        r(pos+7 downto pos)              := hdrs.ipv4.tos;           pos := pos + 8;
        r(pos+15 downto pos)             := hdrs.ipv4.total_length;  pos := pos + 16;
        r(pos+15 downto pos)             := hdrs.ipv4.identification; pos := pos + 16;
        r(pos+2 downto pos)              := hdrs.ipv4.flags;         pos := pos + 3;
        r(pos+12 downto pos)             := hdrs.ipv4.fragment_offset; pos := pos + 13;
        r(pos+7 downto pos)              := hdrs.ipv4.ttl;           pos := pos + 8;
        r(pos+7 downto pos)              := hdrs.ipv4.protocol;      pos := pos + 8;
        r(pos+15 downto pos)             := hdrs.ipv4.header_checksum; pos := pos + 16;
        r(pos+31 downto pos)             := hdrs.ipv4.src_ip;        pos := pos + 32;
        r(pos+31 downto pos)             := hdrs.ipv4.dst_ip;        pos := pos + 32;
        r(pos)                           := hdrs.ipv4_vld;           pos := pos + 1;
        r(pos+OFFSET_WIDTH-1 downto pos) := std_logic_vector(hdrs.ipv4_offset(OFFSET_WIDTH-1 downto 0)); pos := pos + OFFSET_WIDTH;
        -- TCP: 16+16+32+32+4+3+9+16+16+16+1+OFFSET_WIDTH bits
        r(pos+15 downto pos)             := hdrs.tcp.src_port;      pos := pos + 16;
        r(pos+15 downto pos)             := hdrs.tcp.dst_port;      pos := pos + 16;
        r(pos+31 downto pos)             := hdrs.tcp.seq_num;       pos := pos + 32;
        r(pos+31 downto pos)             := hdrs.tcp.ack_num;       pos := pos + 32;
        r(pos+3 downto pos)              := hdrs.tcp.data_offset;   pos := pos + 4;
        r(pos+2 downto pos)              := hdrs.tcp.reserved;      pos := pos + 3;
        r(pos+8 downto pos)              := hdrs.tcp.flags;         pos := pos + 9;
        r(pos+15 downto pos)             := hdrs.tcp.window;        pos := pos + 16;
        r(pos+15 downto pos)             := hdrs.tcp.checksum;      pos := pos + 16;
        r(pos+15 downto pos)             := hdrs.tcp.urgent_ptr;    pos := pos + 16;
        r(pos)                           := hdrs.tcp_vld;           pos := pos + 1;
        r(pos+OFFSET_WIDTH-1 downto pos) := std_logic_vector(hdrs.tcp_offset(OFFSET_WIDTH-1 downto 0));
        return r(pos-1 downto 0);
    end function;

    -- Convert std_logic_vector to extracted_headers_t record for deserialization
    -- OFFSET_WIDTH specifies the actual width of offset fields to use (must be <= MAX_OFFSET_WIDTH)
    function slv_to_extracted_headers (slv : std_logic_vector; OFFSET_WIDTH : natural) return extracted_headers_t is
        variable r   : extracted_headers_t;
        variable pos : natural := 0;
    begin
        r.eth.dst_mac          := slv(pos+47 downto pos);      pos := pos + 48;
        r.eth.src_mac          := slv(pos+47 downto pos);      pos := pos + 48;
        r.eth.ethertype        := slv(pos+15 downto pos);      pos := pos + 16;
        r.eth_vld              := slv(pos);                    pos := pos + 1;
        r.eth_offset           := unsigned(slv(pos+OFFSET_WIDTH-1 downto pos)); pos := pos + OFFSET_WIDTH;
        r.vlan.tci             := slv(pos+15 downto pos);      pos := pos + 16;
        r.vlan.ethertype       := slv(pos+15 downto pos);      pos := pos + 16;
        r.vlan_vld             := slv(pos);                    pos := pos + 1;
        r.vlan_offset          := unsigned(slv(pos+OFFSET_WIDTH-1 downto pos)); pos := pos + OFFSET_WIDTH;
        r.ipv4.version         := slv(pos+3 downto pos);       pos := pos + 4;
        r.ipv4.ihl             := slv(pos+3 downto pos);       pos := pos + 4;
        r.ipv4.tos             := slv(pos+7 downto pos);       pos := pos + 8;
        r.ipv4.total_length    := slv(pos+15 downto pos);      pos := pos + 16;
        r.ipv4.identification  := slv(pos+15 downto pos);      pos := pos + 16;
        r.ipv4.flags           := slv(pos+2 downto pos);       pos := pos + 3;
        r.ipv4.fragment_offset := slv(pos+12 downto pos);      pos := pos + 13;
        r.ipv4.ttl             := slv(pos+7 downto pos);       pos := pos + 8;
        r.ipv4.protocol        := slv(pos+7 downto pos);       pos := pos + 8;
        r.ipv4.header_checksum := slv(pos+15 downto pos);      pos := pos + 16;
        r.ipv4.src_ip          := slv(pos+31 downto pos);      pos := pos + 32;
        r.ipv4.dst_ip          := slv(pos+31 downto pos);      pos := pos + 32;
        r.ipv4_vld             := slv(pos);                    pos := pos + 1;
        r.ipv4_offset          := unsigned(slv(pos+OFFSET_WIDTH-1 downto pos)); pos := pos + OFFSET_WIDTH;
        r.tcp.src_port         := slv(pos+15 downto pos);      pos := pos + 16;
        r.tcp.dst_port         := slv(pos+15 downto pos);      pos := pos + 16;
        r.tcp.seq_num          := slv(pos+31 downto pos);      pos := pos + 32;
        r.tcp.ack_num          := slv(pos+31 downto pos);      pos := pos + 32;
        r.tcp.data_offset      := slv(pos+3 downto pos);       pos := pos + 4;
        r.tcp.reserved         := slv(pos+2 downto pos);       pos := pos + 3;
        r.tcp.flags            := slv(pos+8 downto pos);       pos := pos + 9;
        r.tcp.window           := slv(pos+15 downto pos);      pos := pos + 16;
        r.tcp.checksum         := slv(pos+15 downto pos);      pos := pos + 16;
        r.tcp.urgent_ptr       := slv(pos+15 downto pos);      pos := pos + 16;
        r.tcp_vld              := slv(pos);                    pos := pos + 1;
        r.tcp_offset           := unsigned(slv(pos+OFFSET_WIDTH-1 downto pos));
        return r;
    end function;

end package body;
