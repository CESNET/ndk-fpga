-- axis_eth_parser.vhd: AXI-Stream Ethernet Header Parser
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
use work.axis_eth_parser_types.all;

-- The AXIS_ETH_PARSER component parses Ethernet frames and extracts the
-- Ethernet, VLAN, IPv4, TCP and UDP headers. It contains AXIS_ETH_PARSER_GEN
-- with one stage for each of these protocols, so it reads at most one VLAN tag.
-- The headers are decoded into the extracted_headers_t record on the HEADERS
-- output interface. The original frame data passes through unchanged to the TX
-- interface.
--
entity AXIS_ETH_PARSER is
    generic (
        -- Width of the AXI-Stream data bus in bits (e.g., 256, 512)
        AXI_TDATA_WIDTH : natural := 512;
        -- Maximum packet size in bytes (determines offset field width)
        -- Maximum supported value is 2**14.
        PKT_MTU         : natural := 2**14;
        -- Depth of internal FIFOs (number of packets that can be buffered)
        FIFO_DEPTH      : natural := 64;
        -- Target device family for FIFO implementation (e.g., "AGILEX", "ULTRASCALE")
        DEVICE          : string  := "AGILEX"
    );
    port (
        -- System clock
        CLK           : in  std_logic;
        -- Active-high synchronous reset
        RESET         : in  std_logic;

        -- RX AXI-Stream Interface
        RX_AXI_TDATA  : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP  : in  std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        RX_AXI_TLAST  : in  std_logic;
        RX_AXI_TVALID : in  std_logic;
        RX_AXI_TREADY : out std_logic;

        -- TX AXI-Stream Interface
        TX_AXI_TDATA  : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP  : out std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        TX_AXI_TLAST  : out std_logic;
        TX_AXI_TVALID : out std_logic;
        TX_AXI_TREADY : in  std_logic;

        -- Headers Output Interface
        HEADERS       : out extracted_headers_t;
        HEADERS_VLD   : out std_logic;
        HEADERS_READY : in  std_logic
    );
end entity;

architecture FULL of AXIS_ETH_PARSER is

    constant PROTOCOLS    : proto_array_t := (PROTO_ETH, PROTO_VLAN, PROTO_IPV4, PROTO_TCP, PROTO_UDP);
    constant ETH_I        : natural := get_stage_index(PROTOCOLS, PROTO_ETH);
    constant VLAN_I       : natural := get_stage_index(PROTOCOLS, PROTO_VLAN);
    constant IPV4_I       : natural := get_stage_index(PROTOCOLS, PROTO_IPV4);
    constant TCP_I        : natural := get_stage_index(PROTOCOLS, PROTO_TCP);
    constant UDP_I        : natural := get_stage_index(PROTOCOLS, PROTO_UDP);
    constant OFFSET_WIDTH : natural := log2(PKT_MTU+1);

    signal hdr_data   : slv_array_t(PROTOCOLS'length-1 downto 0)(get_max_extract_bytes(PROTOCOLS)*8-1 downto 0);
    signal hdr_offset : slv_array_t(PROTOCOLS'length-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    signal hdr_found  : std_logic_vector(PROTOCOLS'length-1 downto 0);

begin

    parser_i : entity work.AXIS_ETH_PARSER_GEN
    generic map (
        AXI_TDATA_WIDTH => AXI_TDATA_WIDTH,
        PROTOCOLS       => PROTOCOLS,
        -- No register stages, the latency stays the same as before AXIS_ETH_PARSER_GEN
        STAGE_REG_AUTO  => false,
        PKT_MTU         => PKT_MTU,
        FIFO_DEPTH      => FIFO_DEPTH,
        DEVICE          => DEVICE
    )
    port map (
        CLK           => CLK,
        RESET         => RESET,

        RX_AXI_TDATA  => RX_AXI_TDATA,
        RX_AXI_TKEEP  => RX_AXI_TKEEP,
        RX_AXI_TLAST  => RX_AXI_TLAST,
        RX_AXI_TVALID => RX_AXI_TVALID,
        RX_AXI_TREADY => RX_AXI_TREADY,

        TX_AXI_TDATA  => TX_AXI_TDATA,
        TX_AXI_TKEEP  => TX_AXI_TKEEP,
        TX_AXI_TLAST  => TX_AXI_TLAST,
        TX_AXI_TVALID => TX_AXI_TVALID,
        TX_AXI_TREADY => TX_AXI_TREADY,

        HDR_DATA      => hdr_data,
        HDR_OFFSET    => hdr_offset,
        HDR_FOUND     => hdr_found,
        HDR_VLD       => HEADERS_VLD,
        HDR_READY     => HEADERS_READY
    );

    HEADERS.eth         <= decode_eth(hdr_data(ETH_I));
    HEADERS.eth_vld     <= hdr_found(ETH_I);
    HEADERS.eth_offset  <= resize(unsigned(hdr_offset(ETH_I)), MAX_OFFSET_WIDTH);

    HEADERS.vlan        <= decode_vlan(hdr_data(VLAN_I));
    HEADERS.vlan_vld    <= hdr_found(VLAN_I);
    HEADERS.vlan_offset <= resize(unsigned(hdr_offset(VLAN_I)), MAX_OFFSET_WIDTH);

    HEADERS.ipv4        <= decode_ipv4(hdr_data(IPV4_I));
    HEADERS.ipv4_vld    <= hdr_found(IPV4_I);
    HEADERS.ipv4_offset <= resize(unsigned(hdr_offset(IPV4_I)), MAX_OFFSET_WIDTH);

    HEADERS.tcp         <= decode_tcp(hdr_data(TCP_I));
    HEADERS.tcp_vld     <= hdr_found(TCP_I);
    HEADERS.tcp_offset  <= resize(unsigned(hdr_offset(TCP_I)), MAX_OFFSET_WIDTH);

    HEADERS.udp         <= decode_udp(hdr_data(UDP_I));
    HEADERS.udp_vld     <= hdr_found(UDP_I);
    HEADERS.udp_offset  <= resize(unsigned(hdr_offset(UDP_I)), MAX_OFFSET_WIDTH);

end architecture;
