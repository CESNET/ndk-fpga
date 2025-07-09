-- rx_pipeline.vhd: AXIS_RX_PIPELINE component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;
use work.type_pack.all;
use work.proto_hdr_pack.all;
use work.proto_match_pack.all;

entity AXIS_RX_PIPELINE is
    generic (
        -- Configuration array object.
        CONFIG                : config_array_t := CONFIG_NONE;
        -- >>>> DO NOT MODIFY => EXPLANATORY PURPOSE ONLY!
        -- Number of match-action tables per port.
        CONFIG_SIZE           : natural        := tsel(CONFIG(0).match_num_fields = 0, 0, CONFIG'length);
        -- Max capacity of the match-action tables.
        CONFIG_MAX_ITEMS      : natural        := config_array_get_max(CONFIG, MAT_CONFIG_ITEMS);
        -- Max address width in bits.
        CONFIG_MAX_ADDR_WIDTH : natural        := log2(CONFIG_MAX_ITEMS);
        -- Max data vector width in bits.
        CONFIG_MAX_DATA_WIDTH : natural        := config_array_get_max(CONFIG, MAT_CONFIG_MATCH_WIDTH);
        -- <<<<
        -- AXI-Stream data bus width in bits.
        AXI_TDATA_WIDTH       : natural        := 512;
        -- AXI-Stream destination width in bits (switch purposes only).
        -- TODO: change this to common AXI_TUSER_WIDTH?
        AXI_TDEST_WIDTH       : natural        := 1;
        -- Enable read from match-action tables.
        MAT_READ_ENABLE       : boolean        := true;
        -- Number of output ports.
        NUM_PORTS             : natural        := 2**AXI_TDEST_WIDTH;
        -- Depth of individual virtual output queues.
        NUM_ITEMS_PER_PORT    : integer_vector := (0 => 16, 1 => 16);
        -- Maximum capacity width in bits.
        MAX_STATUS_WIDTH      : integer        := log2(max(NUM_ITEMS_PER_PORT))+1;
        -- Target device.
        DEVICE                : string         := "AGILEX"
    );
    port (
        -- =========================================================================
        -- CLOCK AND RESET
        -- =========================================================================
        CLK              : in  std_logic;
        RESET            : in  std_logic;

        -- =========================================================================
        -- RX AXI INTERFACE
        -- =========================================================================
        RX_AXI_TDATA     : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP     : in  std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TLAST     : in  std_logic;
        RX_AXI_TVALID    : in  std_logic;
        RX_AXI_TREADY    : out std_logic;

        -- =========================================================================
        -- TX AXI INTERFACE
        -- =========================================================================
        TX_AXI_TDATA     : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP     : out std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TLAST     : out std_logic;
        TX_AXI_TVALID    : out std_logic;
        TX_AXI_TREADY    : in  std_logic;

        -- =========================================================================
        -- MATCH-ACTION TABLES READ/WRITE INTERFACE
        -- =========================================================================
        MAT_READ_ADDR    : in  std_logic_vector(CONFIG_MAX_ADDR_WIDTH-1 downto 0);
        MAT_READ_EN      : in  std_logic_vector(CONFIG_SIZE-1 downto 0);
        MAT_READ_RDY     : out std_logic_vector(CONFIG_SIZE-1 downto 0);
        MAT_READ_VLD     : out std_logic_vector(CONFIG_SIZE-1 downto 0);
        MAT_READ_DATA    : out std_logic_vector(CONFIG_SIZE*CONFIG_MAX_DATA_WIDTH-1 downto 0);
        MAT_READ_MASK    : out std_logic_vector(CONFIG_SIZE*CONFIG_MAX_DATA_WIDTH-1 downto 0);
        MAT_READ_ACTION  : out std_logic_vector(CONFIG_SIZE*AXI_TDEST_WIDTH-1 downto 0);

        MAT_WRITE_ADDR   : in  std_logic_vector(CONFIG_MAX_ADDR_WIDTH-1 downto 0);
        MAT_WRITE_EN     : in  std_logic_vector(CONFIG_SIZE-1 downto 0);
        MAT_WRITE_RDY    : out std_logic_vector(CONFIG_SIZE-1 downto 0);
        MAT_WRITE_DATA   : in  std_logic_vector(CONFIG_MAX_DATA_WIDTH-1 downto 0);
        MAT_WRITE_MASK   : in  std_logic_vector(CONFIG_MAX_DATA_WIDTH-1 downto 0);
        MAT_WRITE_ACTION : in  std_logic_vector(AXI_TDEST_WIDTH-1 downto 0);

        -- =========================================================================
        -- PORT-MATCHING CONTROL INTERFACE
        -- =========================================================================
        DEST_REQ_VEC     : out std_logic_vector(NUM_PORTS-1 downto 0);
        DEST_REQ_SIZES   : out std_logic_vector(NUM_PORTS*MAX_STATUS_WIDTH-1 downto 0) := (others => '0');
        VOQ_CONN_VLD     : in  std_logic;
        VOQ_CONN_SEL     : in  std_logic_vector(AXI_TDEST_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of AXIS_RX_PIPELINE is

    signal s_parser_tx_axi_tdata      : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal s_parser_tx_axi_tkeep      : std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
    signal s_parser_tx_axi_tlast      : std_logic;
    signal s_parser_tx_axi_tvalid     : std_logic;
    signal s_parser_tx_axi_tready     : std_logic;
    signal s_parser_hdr_mac           : std_logic_vector(MAC_HDR_W-1 downto 0);
    signal s_parser_hdr_mac_vld       : std_logic;
    signal s_parser_hdr_vlan1         : std_logic_vector(VLAN_HDR_W-1 downto 0);
    signal s_parser_hdr_vlan1_vld     : std_logic;
    signal s_parser_hdr_vlan2         : std_logic_vector(VLAN_HDR_W-1 downto 0);
    signal s_parser_hdr_vlan2_vld     : std_logic;
    -- signal s_parser_payload_ptr       : std_logic_vector(log2(AXI_TDATA_WIDTH/8)-1 downto 0);
    signal s_parser_headers_src_rdy   : std_logic;
    signal s_parser_headers_dst_rdy   : std_logic;

    signal s_dispatcher_tx_axi_tdata  : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal s_dispatcher_tx_axi_tkeep  : std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
    signal s_dispatcher_tx_axi_tdest  : std_logic_vector(AXI_TDEST_WIDTH-1 downto 0);
    signal s_dispatcher_tx_axi_tlast  : std_logic;
    signal s_dispatcher_tx_axi_tvalid : std_logic;
    signal s_dispatcher_tx_axi_tready : std_logic;

begin

    axis_parser_i : entity work.AXIS_PARSER
    generic map (
        AXI_TDATA_WIDTH => AXI_TDATA_WIDTH,
        DEVICE          => DEVICE
    )
    port map (
        CLK             => CLK,
        RESET           => RESET,
        RX_AXI_TDATA    => RX_AXI_TDATA,
        RX_AXI_TKEEP    => RX_AXI_TKEEP,
        RX_AXI_TLAST    => RX_AXI_TLAST,
        RX_AXI_TVALID   => RX_AXI_TVALID,
        RX_AXI_TREADY   => RX_AXI_TREADY,
        TX_AXI_TDATA    => s_parser_tx_axi_tdata,
        TX_AXI_TKEEP    => s_parser_tx_axi_tkeep,
        TX_AXI_TLAST    => s_parser_tx_axi_tlast,
        TX_AXI_TVALID   => s_parser_tx_axi_tvalid,
        TX_AXI_TREADY   => s_parser_tx_axi_tready,
        HDR_MAC         => s_parser_hdr_mac,
        HDR_MAC_VLD     => s_parser_hdr_mac_vld,
        HDR_VLAN1       => s_parser_hdr_vlan1,
        HDR_VLAN1_VLD   => s_parser_hdr_vlan1_vld,
        HDR_VLAN2       => s_parser_hdr_vlan2,
        HDR_VLAN2_VLD   => s_parser_hdr_vlan2_vld,
        PAYLOAD_PTR     => open,
        HEADERS_SRC_RDY => s_parser_headers_src_rdy
    );

    axis_dispatcher_i : entity work.AXIS_DISPATCHER
    generic map (
        CONFIG           => CONFIG,
        AXI_TDATA_WIDTH  => AXI_TDATA_WIDTH,
        AXI_TDEST_WIDTH  => AXI_TDEST_WIDTH,
        MAT_READ_ENABLE  => MAT_READ_ENABLE,
        DEVICE           => DEVICE
    )
    port map (
        CLK              => CLK,
        RESET            => RESET,
        RX_AXI_TDATA     => s_parser_tx_axi_tdata,
        RX_AXI_TKEEP     => s_parser_tx_axi_tkeep,
        RX_AXI_TLAST     => s_parser_tx_axi_tlast,
        RX_AXI_TVALID    => s_parser_tx_axi_tvalid,
        RX_AXI_TREADY    => s_parser_tx_axi_tready,
        TX_AXI_TDATA     => s_dispatcher_tx_axi_tdata,
        TX_AXI_TKEEP     => s_dispatcher_tx_axi_tkeep,
        TX_AXI_TDEST     => s_dispatcher_tx_axi_tdest,
        TX_AXI_TLAST     => s_dispatcher_tx_axi_tlast,
        TX_AXI_TVALID    => s_dispatcher_tx_axi_tvalid,
        TX_AXI_TREADY    => s_dispatcher_tx_axi_tready,
        HDR_MAC          => s_parser_hdr_mac,
        HDR_MAC_VLD      => s_parser_hdr_mac_vld,
        HDR_VLAN1        => s_parser_hdr_vlan1,
        HDR_VLAN1_VLD    => s_parser_hdr_vlan1_vld,
        HDR_VLAN2        => s_parser_hdr_vlan2,
        HDR_VLAN2_VLD    => s_parser_hdr_vlan2_vld,
        HEADERS_SRC_RDY  => s_parser_headers_src_rdy,
        MAT_READ_ADDR    => MAT_READ_ADDR,
        MAT_READ_EN      => MAT_READ_EN,
        MAT_READ_RDY     => MAT_READ_RDY,
        MAT_READ_VLD     => MAT_READ_VLD,
        MAT_READ_DATA    => MAT_READ_DATA,
        MAT_READ_MASK    => MAT_READ_MASK,
        MAT_READ_ACTION  => MAT_READ_ACTION,
        MAT_WRITE_ADDR   => MAT_WRITE_ADDR,
        MAT_WRITE_EN     => MAT_WRITE_EN,
        MAT_WRITE_RDY    => MAT_WRITE_RDY,
        MAT_WRITE_DATA   => MAT_WRITE_DATA,
        MAT_WRITE_MASK   => MAT_WRITE_MASK,
        MAT_WRITE_ACTION => MAT_WRITE_ACTION
    );

    axis_voq_manager_i : entity work.AXIS_VOQ_MANAGER
    generic map (
        NUM_PORTS          => NUM_PORTS,
        NUM_ITEMS_PER_PORT => NUM_ITEMS_PER_PORT,
        AXI_TDATA_WIDTH    => AXI_TDATA_WIDTH,
        AXI_TDEST_WIDTH    => AXI_TDEST_WIDTH,
        DEVICE             => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,
        RX_AXI_TDATA   => s_dispatcher_tx_axi_tdata,
        RX_AXI_TKEEP   => s_dispatcher_tx_axi_tkeep,
        RX_AXI_TDEST   => s_dispatcher_tx_axi_tdest,
        RX_AXI_TLAST   => s_dispatcher_tx_axi_tlast,
        RX_AXI_TVALID  => s_dispatcher_tx_axi_tvalid,
        RX_AXI_TREADY  => s_dispatcher_tx_axi_tready,
        TX_AXI_TDATA   => TX_AXI_TDATA,
        TX_AXI_TKEEP   => TX_AXI_TKEEP,
        TX_AXI_TLAST   => TX_AXI_TLAST,
        TX_AXI_TVALID  => TX_AXI_TVALID,
        TX_AXI_TREADY  => TX_AXI_TREADY,
        DEST_REQ_VEC   => DEST_REQ_VEC,
        DEST_REQ_SIZES => DEST_REQ_SIZES,
        VOQ_CONN_VLD   => VOQ_CONN_VLD,
        VOQ_CONN_SEL   => VOQ_CONN_SEL
    );

end architecture;
