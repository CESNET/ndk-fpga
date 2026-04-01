-- axis_eth_parser_unit.vhd: AXI-Stream Ethernet Parser Unit
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

-- The AXIS_ETH_PARSER_UNIT component is a single stage in the multi-stage
-- Ethernet header parser pipeline. Each stage extracts header data for one
-- protocol layer (Ethernet, VLAN, IPv4, or TCP) and determines the next
-- protocol in the chain. The component uses the AXIS_ETH_PARSER_SNIFFER to
-- extract raw header bytes from the AXI-Stream data flow. Based on the
-- extracted header content, the next protocol type and byte offset are
-- calculated for subsequent parser stages.
--
entity AXIS_ETH_PARSER_UNIT is
    generic (
        -- Width of the AXI-Stream data bus in bits (e.g., 256, 512)
        AXI_TDATA_WIDTH    : natural := 512;
        -- Width of extracted data field in bits (get_max_extract_bytes * 8)
        EXTRACT_DATA_WIDTH : natural := 160;
        -- Protocol to parse in this stage (PROTO_ETH, PROTO_VLAN, PROTO_IPV4, PROTO_TCP)
        PROTOCOL           : natural := PROTO_ETH;
        -- Maximum packet size in bytes (determines offset field width)
        PKT_MTU            : natural := 2**14;
        -- Target device family for implementation (e.g., "AGILEX", "ULTRASCALE")
        DEVICE             : string  := "AGILEX"
    );
    port (
        -- System clock
        CLK                 : in  std_logic;
        -- Active-high synchronous reset
        RESET               : in  std_logic;

        -- RX AXI-Stream Interface
        RX_AXI_TDATA        : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP        : in  std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TLAST        : in  std_logic;
        RX_AXI_TVALID       : in  std_logic;
        RX_AXI_TREADY       : out  std_logic;

        -- TX AXI-Stream Interface
        TX_AXI_TDATA        : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP        : out std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TLAST        : out std_logic;
        TX_AXI_TVALID       : out std_logic;
        TX_AXI_TREADY       : in  std_logic;

        -- Input protocol chain
        IN_PROTOCOL         : in  std_logic_vector(PROTOCOL_WIDTH-1 downto 0);
        IN_OFFSET           : in  std_logic_vector(log2(PKT_MTU+1)-1 downto 0);
        IN_VLD              : in  std_logic;

        -- Output protocol chain (to next stage)
        NEXT_PROTOCOL       : out std_logic_vector(PROTOCOL_WIDTH-1 downto 0);
        NEXT_OFFSET         : out std_logic_vector(log2(PKT_MTU+1)-1 downto 0);
        NEXT_VLD            : out std_logic;

        -- Extracted header data
        EXTRACTED_DATA        : out std_logic_vector(EXTRACT_DATA_WIDTH-1 downto 0) := (others => '0');
        EXTRACTED_DATA_VLD    : out std_logic;
        EXTRACTED_DATA_OFFSET : out std_logic_vector(log2(PKT_MTU+1)-1 downto 0);
        EXTRACTED_DATA_OK     : out std_logic
    );
end entity;

architecture FULL of AXIS_ETH_PARSER_UNIT is

    -- Width of the offset field in bits (derived from PKT_MTU)
    constant OFFSET_WIDTH        : natural := log2(PKT_MTU+1);
    -- Combined width for metadata (offset + protocol)
    constant META_WIDTH_INTERNAL : natural := OFFSET_WIDTH + PROTOCOL_WIDTH;
    -- Number of bytes to extract for current protocol
    constant STAGE_EXTRACT_BYTES : natural := get_extract_bytes(PROTOCOL);

    signal in_enable           : std_logic;

    -- Extracted data and metadata from sniffer
    signal ext_valid           : std_logic;
    signal ext_meta            : std_logic_vector(META_WIDTH_INTERNAL-1 downto 0);
    signal ext_data            : std_logic_vector(STAGE_EXTRACT_BYTES*8-1 downto 0);
    signal ext_data_resized    : std_logic_vector(EXTRACT_DATA_WIDTH-1 downto 0);
    signal ext_meta_proto      : std_logic_vector(PROTOCOL_WIDTH-1 downto 0);
    signal ext_meta_offset     : std_logic_vector(OFFSET_WIDTH-1 downto 0);

    -- Next protocol type indicators extracted from header
    signal next_type_eth       : std_logic_vector(15 downto 0);
    signal next_type_vlan      : std_logic_vector(15 downto 0);
    signal next_type_ipv4      : std_logic_vector(7 downto 0);

    -- Debug signals
    signal rx_axi_nonfirst_reg : std_logic;
    signal rx_axi_first        : std_logic;
    signal dbg_rx_pkt_cnt      : unsigned(63 downto 0);
    signal dbg_hdr_cnt         : unsigned(63 downto 0);

begin

    in_enable <= '1' when (to_integer(unsigned(IN_PROTOCOL)) = PROTOCOL) else '0';

    -- Sniffer extracts header bytes from AXI-Stream at calculated offset
    sniffer_i : entity work.AXIS_ETH_PARSER_SNIFFER
    generic map (
        AXI_TDATA_WIDTH => AXI_TDATA_WIDTH,
        EXTRACT_BYTES   => STAGE_EXTRACT_BYTES,
        PKT_MTU         => PKT_MTU,
        META_WIDTH      => META_WIDTH_INTERNAL,
        DEVICE          => DEVICE
    )
    port map (
        CLK               => CLK,
        RESET             => RESET,
        RX_AXI_TDATA      => RX_AXI_TDATA,
        RX_AXI_TKEEP      => RX_AXI_TKEEP,
        RX_AXI_TLAST      => RX_AXI_TLAST,
        RX_AXI_TVALID     => RX_AXI_TVALID,
        RX_AXI_TREADY     => RX_AXI_TREADY,
        TX_AXI_TDATA      => TX_AXI_TDATA,
        TX_AXI_TKEEP      => TX_AXI_TKEEP,
        TX_AXI_TLAST      => TX_AXI_TLAST,
        TX_AXI_TVALID     => TX_AXI_TVALID,
        TX_AXI_TREADY     => TX_AXI_TREADY,
        START_META        => std_logic_vector(IN_OFFSET) & std_logic_vector(IN_PROTOCOL),
        START_OFFSET      => std_logic_vector(IN_OFFSET),
        START_ENABLE      => in_enable,
        START_VALID       => IN_VLD,
        EXTRACTED_META    => ext_meta,
        EXTRACTED_DATA    => ext_data,
        EXTRACTED_VALID   => ext_valid
    );

    -- Split metadata into protocol and offset fields
    ext_meta_proto  <= ext_meta(PROTOCOL_WIDTH-1 downto 0);
    ext_meta_offset <= ext_meta(META_WIDTH_INTERNAL-1 downto PROTOCOL_WIDTH);

    -- Resize extracted data to fixed output width (zero-padded)
    ext_data_resized(STAGE_EXTRACT_BYTES*8-1 downto 0) <= ext_data;

    -- Drive output signals
    NEXT_VLD              <= ext_valid;
    EXTRACTED_DATA_VLD    <= ext_valid;
    EXTRACTED_DATA_OFFSET <= ext_meta_offset;
    EXTRACTED_DATA        <= ext_data_resized;

    -- Extract next protocol type indicators from header fields
    next_type_eth  <= ext_data_resized(8*(12+1)-1 downto 8*12) & ext_data_resized(8*(13+1)-1 downto 8*13);
    next_type_vlan <= ext_data_resized(8*(2+1)-1 downto 8*2) & ext_data_resized(8*(3+1)-1 downto 8*3);
    next_type_ipv4 <= ext_data_resized(8*(9+1)-1 downto 8*9);

    -- Calculate next protocol type and offset based on current header content
    process (all)
        variable ip_ihl : unsigned(3 downto 0);
    begin
        NEXT_OFFSET   <= std_logic_vector(unsigned(ext_meta_offset));
        NEXT_PROTOCOL <= ext_meta_proto;

        if ((PROTO_ETH = PROTOCOL) and (to_integer(unsigned(ext_meta_proto)) = PROTOCOL)) then
            NEXT_OFFSET <= std_logic_vector(unsigned(ext_meta_offset) + to_unsigned(ETH_HDR_SIZE, OFFSET_WIDTH));
            if (next_type_eth = ETH_TYPE_VLAN) then
                NEXT_PROTOCOL <= std_logic_vector(to_unsigned(PROTO_VLAN, PROTOCOL_WIDTH));
            elsif (next_type_eth = ETH_TYPE_IPV4) then
                NEXT_PROTOCOL <= std_logic_vector(to_unsigned(PROTO_IPV4, PROTOCOL_WIDTH));
            else
                NEXT_PROTOCOL <= (others => '0');
            end if;
        end if;

        if ((PROTO_VLAN = PROTOCOL) and (to_integer(unsigned(ext_meta_proto)) = PROTOCOL)) then
            NEXT_OFFSET <= std_logic_vector(unsigned(ext_meta_offset) + to_unsigned(VLAN_HDR_SIZE, OFFSET_WIDTH));
            if (next_type_vlan = ETH_TYPE_IPV4) then
                NEXT_PROTOCOL <= std_logic_vector(to_unsigned(PROTO_IPV4, PROTOCOL_WIDTH));
            else
                NEXT_PROTOCOL <= (others => '0');
            end if;
        end if;

        if ((PROTO_IPV4 = PROTOCOL) and (to_integer(unsigned(ext_meta_proto)) = PROTOCOL)) then
            ip_ihl := unsigned(ext_data_resized(0*8+3 downto 0));
            if ((next_type_ipv4 = IPV4_PROTO_TCP)) then
                NEXT_PROTOCOL <= std_logic_vector(to_unsigned(PROTO_TCP, PROTOCOL_WIDTH));
            else
                NEXT_PROTOCOL <= (others => '0');
            end if;
            -- Validate IHL: minimum is 5 (20 bytes), maximum is 15 (60 bytes)
            if ((ip_ihl >= 5) and (ip_ihl <= 15)) then
                NEXT_OFFSET <= std_logic_vector(unsigned(ext_meta_offset) + to_unsigned(to_integer(ip_ihl) * 4, OFFSET_WIDTH));
            else
                NEXT_OFFSET <= std_logic_vector(unsigned(ext_meta_offset) + to_unsigned(IPV4_HDR_MIN_SIZE, OFFSET_WIDTH));
            end if;
        end if;
    end process;

    -- Set valid flag when expected protocol matches actual protocol
    process (all)
    begin
        if (to_integer(unsigned(ext_meta_proto)) = PROTOCOL) then
            EXTRACTED_DATA_OK <= '1';
        else
            EXTRACTED_DATA_OK <= '0';
        end if;
    end process;

    -- Debug counters for packet and header statistics (synthesis disabled)
    -- pragma synthesis_off
    process (CLK)
    begin
        if rising_edge(CLK) then
            if ((RESET = '1') or (RX_AXI_TLAST = '1' and RX_AXI_TVALID = '1' and RX_AXI_TREADY = '1')) then
                rx_axi_nonfirst_reg <= '0';
            elsif (RX_AXI_TVALID = '1' and RX_AXI_TREADY = '1') then
                rx_axi_nonfirst_reg <= '1';
            end if;
        end if;
    end process;

    rx_axi_first <= RX_AXI_TVALID and RX_AXI_TREADY and not rx_axi_nonfirst_reg;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_rx_pkt_cnt <= (others => '0');
            elsif (rx_axi_first = '1') then
                dbg_rx_pkt_cnt <= dbg_rx_pkt_cnt + 1;
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_hdr_cnt <= (others => '0');
            elsif (ext_valid = '1') then
                dbg_hdr_cnt <= dbg_hdr_cnt + 1;
            end if;
        end if;
    end process;
    -- pragma synthesis_on

end architecture;
