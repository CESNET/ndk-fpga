-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                           Description
-- ----------------------------------------------------------------------------

-- This module performs parallel calculation of L3 and L4 checksums.
-- It takes an MFB stream with packets and an MVB stream with metadata,
-- merges them using METADATA_INSERTOR, duplicates the stream using
-- MFB_DUPLICATION, and processes both streams in parallel through
-- MFB_CHECKSUM_L3 and MFB_CHECKSUM_L4 modules. The outputs are then
-- merged using MVB_MERGE_ITEMS to produce a single MVB interface with
-- both L3 and L4 checksum results.
--
entity MFB_CHECKSUM_L3L4 is
    generic (
        -- Number of Regions within a data word, must be power of 2.
        MFB_REGIONS      : natural := 4;
        -- Region size (in Blocks).
        MFB_REGION_SIZE  : natural := 8;
        -- Block size (in Items).
        MFB_BLOCK_SIZE   : natural := 8;
        -- Item width (in bits), must be 8.
        MFB_ITEM_WIDTH   : natural := 8;
        -- Maximum size of a packet (in Items).
        PKT_MTU          : natural := 2**14;
        -- Width of packet length signal in bits (must be log2(PKT_MTU+1)).
        PKT_LENGTH_WIDTH : natural := log2(PKT_MTU+1);
        -- Width of L3 offset signal in bits.
        L3_OFFSET_WIDTH  : natural := 10;
        -- Width of L3 length signal in bits.
        L3_LENGTH_WIDTH  : natural := 13;
        -- Width of L4 offset signal in bits.
        L4_OFFSET_WIDTH  : natural := 10;
        -- Width of L4 length signal in bits.
        L4_LENGTH_WIDTH  : natural := 13;
        -- FPGA device name.
        -- Options: ULTRASCALE, STRATIX10, AGILEX, ...
        DEVICE           : string := "AGILEX"
    );
    port (
        -- ========================================================================
        -- Clock and Reset
        -- ========================================================================

        CLK                 : in  std_logic;
        RESET               : in  std_logic;

        -- ========================================================================
        -- RX MFB interface (packet data)
        -- ========================================================================

        RX_MFB_DATA         : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF_POS      : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS      : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SOF          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SRC_RDY      : in  std_logic;
        RX_MFB_DST_RDY      : out std_logic;

        -- ========================================================================
        -- RX MVB interface (metadata for each packet)
        -- ========================================================================

        -- L3 checksum original value.
        RX_MVB_L3_CSUM_ORIG : in  std_logic_vector(MFB_REGIONS*16-1 downto 0);
        -- Enable L3 checksum calculation.
        RX_MVB_L3_CSUM_EN   : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- Offset of the L3 header (from SOF).
        RX_MVB_L3_OFFSET    : in  std_logic_vector(MFB_REGIONS*L3_OFFSET_WIDTH-1 downto 0);
        -- Length of the L3 header (from SOF).
        RX_MVB_L3_LENGTH    : in  std_logic_vector(MFB_REGIONS*L3_LENGTH_WIDTH-1 downto 0);

        -- L4 checksum original value.
        RX_MVB_L4_CSUM_ORIG : in  std_logic_vector(MFB_REGIONS*16-1 downto 0);
        -- Enable L4 checksum calculation.
        RX_MVB_L4_CSUM_EN   : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- Offset of the L4 protocol (from SOF).
        RX_MVB_L4_OFFSET    : in  std_logic_vector(MFB_REGIONS*L4_OFFSET_WIDTH-1 downto 0);
        -- Length of the L4 protocol (from SOF).
        RX_MVB_L4_LENGTH    : in  std_logic_vector(MFB_REGIONS*L4_LENGTH_WIDTH-1 downto 0);
        -- L4 protocol number (required for pseudo-header).
        RX_MVB_L4_PROTOCOL  : in  std_logic_vector(MFB_REGIONS*8-1 downto 0);
        -- Source IP address (required for pseudo-header).
        RX_MVB_IP_SRC_ADDR  : in  std_logic_vector(MFB_REGIONS*128-1 downto 0);
        -- Destination IP address (required for pseudo-header).
        RX_MVB_IP_DST_ADDR  : in  std_logic_vector(MFB_REGIONS*128-1 downto 0);
        -- Indicates if the packet is IPv6.
        RX_MVB_IP_VER6      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- Packet length (in Items) for each packet.
        RX_MVB_PKT_LENGTH   : in  std_logic_vector(MFB_REGIONS*PKT_LENGTH_WIDTH-1 downto 0);

        -- MVB valid and ready signals.
        RX_MVB_VLD          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MVB_SRC_RDY      : in  std_logic;
        RX_MVB_DST_RDY      : out std_logic;

        -- ========================================================================
        -- TX MVB interface (checksum results)
        -- ========================================================================

        -- L3 checksum calculated value.
        TX_MVB_L3_CSUM      : out std_logic_vector(MFB_REGIONS*16-1 downto 0);
        -- L3 checksum comparison result (OK).
        TX_MVB_L3_CSUM_OK   : out std_logic_vector(MFB_REGIONS-1 downto 0);
        -- L3 checksum calculation permission (EN).
        TX_MVB_L3_CSUM_EN   : out std_logic_vector(MFB_REGIONS-1 downto 0);

        -- L4 checksum calculated value.
        TX_MVB_L4_CSUM      : out std_logic_vector(MFB_REGIONS*16-1 downto 0);
        -- L4 checksum comparison result (OK).
        TX_MVB_L4_CSUM_OK   : out std_logic_vector(MFB_REGIONS-1 downto 0);
        -- L4 checksum calculation permission (EN).
        TX_MVB_L4_CSUM_EN   : out std_logic_vector(MFB_REGIONS-1 downto 0);

        -- MVB valid and ready signals.
        TX_MVB_VLD          : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MVB_SRC_RDY      : out std_logic;
        TX_MVB_DST_RDY      : in  std_logic
    );
end entity;

architecture FULL of MFB_CHECKSUM_L3L4 is

    -- -------------------------------------------------------------------------
    -- Constants
    -- -------------------------------------------------------------------------

    -- Total width of metadata inserted into MFB
    -- L3: 16 (CSUM_ORIG) + 1 (CSUM_EN) + 7 (OFFSET) + 12 (LENGTH) = 36 bits
    -- L4: 16 (CSUM_ORIG) + 1 (CSUM_EN) + 8 (OFFSET) + 12 (LENGTH) + 8 (PROTOCOL) + 128 (SRC_ADDR) + 128 (DST_ADDR) + 1 (IP_VER6) = 302 bits
    -- PKT: PKT_LENGTH_WIDTH bits
    constant L3_META_WIDTH : natural := 16 + 1 + L3_OFFSET_WIDTH + L3_LENGTH_WIDTH;
    constant L4_META_WIDTH : natural := 16 + 1 + L4_OFFSET_WIDTH + L4_LENGTH_WIDTH + 8 + 128 + 128 + 1;
    constant META_WIDTH    : natural := L3_META_WIDTH + L4_META_WIDTH + PKT_LENGTH_WIDTH;

    -- -------------------------------------------------------------------------
    -- Signals for METADATA_INSERTOR
    -- -------------------------------------------------------------------------

    signal mi_mvb_data     : std_logic_vector(MFB_REGIONS*META_WIDTH-1 downto 0);
    signal mi_mvb_vld      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mi_mvb_src_rdy  : std_logic;
    signal mi_mvb_dst_rdy  : std_logic;

    signal mi_mfb_data     : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal mi_mfb_meta     : std_logic_vector(MFB_REGIONS*META_WIDTH-1 downto 0);
    signal mi_mfb_sof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mi_mfb_eof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mi_mfb_sof_pos  : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal mi_mfb_eof_pos  : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal mi_mfb_src_rdy  : std_logic;
    signal mi_mfb_dst_rdy  : std_logic;

    -- -------------------------------------------------------------------------
    -- Signals for MFB_DUPLICATION
    -- -------------------------------------------------------------------------

    signal dup_mfb_data0    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal dup_mfb_sof_pos0 : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal dup_mfb_eof_pos0 : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal dup_mfb_sof0     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal dup_mfb_eof0     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal dup_mfb_src_rdy0 : std_logic;
    signal dup_mfb_dst_rdy0 : std_logic;

    signal dup_mfb_data1    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal dup_mfb_sof_pos1 : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal dup_mfb_eof_pos1 : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal dup_mfb_sof1     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal dup_mfb_eof1     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal dup_mfb_src_rdy1 : std_logic;
    signal dup_mfb_dst_rdy1 : std_logic;

    -- -------------------------------------------------------------------------
    -- Signals for MFB_CHECKSUM_L3
    -- -------------------------------------------------------------------------

    signal l3_csum_orig_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal l3_csum_en_arr      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal l3_offset_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(L3_OFFSET_WIDTH-1 downto 0);
    signal l3_length_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(L3_LENGTH_WIDTH-1 downto 0);
    signal l3_offset_fix_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(L3_OFFSET_WIDTH-1 downto 0);
    signal l3_length_fix_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(L3_LENGTH_WIDTH-1 downto 0);
    signal l3_pkt_length_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(PKT_LENGTH_WIDTH-1 downto 0);
    signal l3_offset_overflow  : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal l3_mvb_csum         : std_logic_vector(MFB_REGIONS*16-1 downto 0);
    signal l3_mvb_csum_ok      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal l3_mvb_csum_en      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal l3_mvb_vld          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal l3_mvb_src_rdy      : std_logic;
    signal l3_mvb_dst_rdy      : std_logic;

    -- -------------------------------------------------------------------------
    -- Signals for MFB_CHECKSUM_L4
    -- -------------------------------------------------------------------------

    signal l4_csum_orig_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal l4_csum_en_arr      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal l4_offset_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(L4_OFFSET_WIDTH-1 downto 0);
    signal l4_length_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(L4_LENGTH_WIDTH-1 downto 0);
    signal l4_offset_fix_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(L4_OFFSET_WIDTH-1 downto 0);
    signal l4_length_fix_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(L4_LENGTH_WIDTH-1 downto 0);
    signal l4_pkt_length_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(PKT_LENGTH_WIDTH-1 downto 0);
    signal l4_offset_overflow  : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal l4_protocol_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(8-1 downto 0);
    signal l4_ip_src_addr_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(128-1 downto 0);
    signal l4_ip_dst_addr_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(128-1 downto 0);
    signal l4_ip_ver6_arr      : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal l4_mvb_csum         : std_logic_vector(MFB_REGIONS*16-1 downto 0);
    signal l4_mvb_csum_ok      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal l4_mvb_csum_en      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal l4_mvb_vld          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal l4_mvb_src_rdy      : std_logic;
    signal l4_mvb_dst_rdy      : std_logic;

    -- -------------------------------------------------------------------------
    -- Arrays for RX MVB signals (deserialized)
    -- -------------------------------------------------------------------------

    signal rx_mvb_l3_csum_orig_arr : slv_array_t(MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal rx_mvb_l3_csum_en_arr   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mvb_l3_offset_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(L3_OFFSET_WIDTH-1 downto 0);
    signal rx_mvb_l3_length_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(L3_LENGTH_WIDTH-1 downto 0);

    signal rx_mvb_l4_csum_orig_arr : slv_array_t(MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal rx_mvb_l4_csum_en_arr   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mvb_l4_offset_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(L4_OFFSET_WIDTH-1 downto 0);
    signal rx_mvb_l4_length_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(L4_LENGTH_WIDTH-1 downto 0);
    signal rx_mvb_l4_protocol_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(8-1 downto 0);
    signal rx_mvb_ip_src_addr_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(128-1 downto 0);
    signal rx_mvb_ip_dst_addr_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(128-1 downto 0);
    signal rx_mvb_ip_ver6_arr      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mvb_pkt_length_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(PKT_LENGTH_WIDTH-1 downto 0);

    -- -------------------------------------------------------------------------
    -- Arrays for metadata assembly/extraction
    -- -------------------------------------------------------------------------

    signal meta_arr        : slv_array_t(MFB_REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal mi_mfb_meta_arr : slv_array_t(MFB_REGIONS-1 downto 0)(META_WIDTH-1 downto 0);

    -- -------------------------------------------------------------------------
    -- Signals for MVB_MERGE_ITEMS
    -- -------------------------------------------------------------------------

    signal merge_rx0_data     : slv_array_t(MFB_REGIONS-1 downto 0)(18-1 downto 0); -- 16 (CSUM) + 1 (OK) + 1 (EN)
    signal merge_rx1_data     : slv_array_t(MFB_REGIONS-1 downto 0)(18-1 downto 0);
    signal merge_tx_data0_slv : std_logic_vector(MFB_REGIONS*18-1 downto 0);
    signal merge_tx_data1_slv : std_logic_vector(MFB_REGIONS*18-1 downto 0);
    signal merge_tx_data0     : slv_array_t(MFB_REGIONS-1 downto 0)(18-1 downto 0);
    signal merge_tx_data1     : slv_array_t(MFB_REGIONS-1 downto 0)(18-1 downto 0);
    signal merge_tx_vld       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal merge_tx_src_rdy   : std_logic;
    signal merge_tx_dst_rdy   : std_logic;

begin

    -- =========================================================================
    -- Deserialize RX MVB signals to slv_array_t
    -- =========================================================================

    rx_mvb_l3_csum_orig_arr <= slv_array_deser(RX_MVB_L3_CSUM_ORIG, MFB_REGIONS);
    rx_mvb_l3_csum_en_arr   <= RX_MVB_L3_CSUM_EN;
    rx_mvb_l3_offset_arr    <= slv_array_deser(RX_MVB_L3_OFFSET, MFB_REGIONS);
    rx_mvb_l3_length_arr    <= slv_array_deser(RX_MVB_L3_LENGTH, MFB_REGIONS);

    rx_mvb_l4_csum_orig_arr <= slv_array_deser(RX_MVB_L4_CSUM_ORIG, MFB_REGIONS);
    rx_mvb_l4_csum_en_arr   <= RX_MVB_L4_CSUM_EN;
    rx_mvb_l4_offset_arr    <= slv_array_deser(RX_MVB_L4_OFFSET, MFB_REGIONS);
    rx_mvb_l4_length_arr    <= slv_array_deser(RX_MVB_L4_LENGTH, MFB_REGIONS);
    rx_mvb_l4_protocol_arr  <= slv_array_deser(RX_MVB_L4_PROTOCOL, MFB_REGIONS);
    rx_mvb_ip_src_addr_arr  <= slv_array_deser(RX_MVB_IP_SRC_ADDR, MFB_REGIONS);
    rx_mvb_ip_dst_addr_arr  <= slv_array_deser(RX_MVB_IP_DST_ADDR, MFB_REGIONS);
    rx_mvb_ip_ver6_arr      <= RX_MVB_IP_VER6;
    rx_mvb_pkt_length_arr   <= slv_array_deser(RX_MVB_PKT_LENGTH, MFB_REGIONS);

    -- =========================================================================
    -- Assemble MVB metadata for METADATA_INSERTOR
    -- =========================================================================

    mi_mvb_data_g : for i in 0 to MFB_REGIONS-1 generate
    begin
        -- L3 metadata: CSUM_ORIG(16) & CSUM_EN(1) & OFFSET(L3_OFFSET_WIDTH) & LENGTH(L3_LENGTH_WIDTH)
        -- L4 metadata: CSUM_ORIG(16) & CSUM_EN(1) & OFFSET(L4_OFFSET_WIDTH) & LENGTH(L4_LENGTH_WIDTH) &
        --              PROTOCOL(8) & SRC_ADDR(128) & DST_ADDR(128) & IP_VER6(1)
        -- PKT metadata: PKT_LENGTH(PKT_LENGTH_WIDTH)
        meta_arr(i) <= rx_mvb_l3_csum_orig_arr(i) &
                       rx_mvb_l3_csum_en_arr(i) &
                       rx_mvb_l3_offset_arr(i) &
                       rx_mvb_l3_length_arr(i) &
                       rx_mvb_l4_csum_orig_arr(i) &
                       rx_mvb_l4_csum_en_arr(i) &
                       rx_mvb_l4_offset_arr(i) &
                       rx_mvb_l4_length_arr(i) &
                       rx_mvb_l4_protocol_arr(i) &
                       rx_mvb_ip_src_addr_arr(i) &
                       rx_mvb_ip_dst_addr_arr(i) &
                       rx_mvb_ip_ver6_arr(i) &
                       rx_mvb_pkt_length_arr(i);
    end generate;

    mi_mvb_data <= slv_array_ser(meta_arr);

    mi_mvb_vld     <= RX_MVB_VLD;
    mi_mvb_src_rdy <= RX_MVB_SRC_RDY;
    RX_MVB_DST_RDY <= mi_mvb_dst_rdy;

    -- =========================================================================
    -- METADATA_INSERTOR: Merge MVB metadata into MFB stream
    -- =========================================================================

    metadata_insertor_i : entity work.METADATA_INSERTOR
    generic map (
        MVB_ITEMS       => MFB_REGIONS,
        MVB_ITEM_WIDTH  => META_WIDTH,
        MFB_REGIONS     => MFB_REGIONS,
        MFB_REGION_SIZE => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
        MFB_META_WIDTH  => 0,
        INSERT_MODE     => 0,  -- Insert in SOF Region
        MVB_FIFO_SIZE   => 32,
        MVB_FIFOX_MULTI => True,
        DEVICE          => DEVICE
    )
    port map (
        CLK             => CLK,
        RESET           => RESET,

        RX_MVB_DATA     => mi_mvb_data,
        RX_MVB_VLD      => mi_mvb_vld,
        RX_MVB_SRC_RDY  => mi_mvb_src_rdy,
        RX_MVB_DST_RDY  => mi_mvb_dst_rdy,

        RX_MFB_DATA     => RX_MFB_DATA,
        RX_MFB_META     => (others => '0'),
        RX_MFB_SOF      => RX_MFB_SOF,
        RX_MFB_EOF      => RX_MFB_EOF,
        RX_MFB_SOF_POS  => RX_MFB_SOF_POS,
        RX_MFB_EOF_POS  => RX_MFB_EOF_POS,
        RX_MFB_SRC_RDY  => RX_MFB_SRC_RDY,
        RX_MFB_DST_RDY  => RX_MFB_DST_RDY,

        TX_MFB_DATA     => mi_mfb_data,
        TX_MFB_META     => open,
        TX_MFB_META_NEW => mi_mfb_meta,
        TX_MFB_SOF      => mi_mfb_sof,
        TX_MFB_EOF      => mi_mfb_eof,
        TX_MFB_SOF_POS  => mi_mfb_sof_pos,
        TX_MFB_EOF_POS  => mi_mfb_eof_pos,
        TX_MFB_SRC_RDY  => mi_mfb_src_rdy,
        TX_MFB_DST_RDY  => mi_mfb_dst_rdy
    );

    -- =========================================================================
    -- MFB_DUPLICATION: Duplicate MFB stream for parallel L3 and L4 processing
    -- =========================================================================

    mfb_duplication_i : entity work.MFB_DUPLICATION
    generic map (
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH
    )
    port map (
        CLK         => CLK,
        RST         => RESET,

        RX_DATA     => mi_mfb_data,
        RX_SOF_POS  => mi_mfb_sof_pos,
        RX_EOF_POS  => mi_mfb_eof_pos,
        RX_SOF      => mi_mfb_sof,
        RX_EOF      => mi_mfb_eof,
        RX_SRC_RDY  => mi_mfb_src_rdy,
        RX_DST_RDY  => mi_mfb_dst_rdy,

        TX0_DATA    => dup_mfb_data0,
        TX0_SOF_POS => dup_mfb_sof_pos0,
        TX0_EOF_POS => dup_mfb_eof_pos0,
        TX0_SOF     => dup_mfb_sof0,
        TX0_EOF     => dup_mfb_eof0,
        TX0_SRC_RDY => dup_mfb_src_rdy0,
        TX0_DST_RDY => dup_mfb_dst_rdy0,

        TX1_DATA    => dup_mfb_data1,
        TX1_SOF_POS => dup_mfb_sof_pos1,
        TX1_EOF_POS => dup_mfb_eof_pos1,
        TX1_SOF     => dup_mfb_sof1,
        TX1_EOF     => dup_mfb_eof1,
        TX1_SRC_RDY => dup_mfb_src_rdy1,
        TX1_DST_RDY => dup_mfb_dst_rdy1
    );

    -- =========================================================================
    -- Extract metadata for L3 and L4 checksum modules
    -- =========================================================================

    mi_mfb_meta_arr <= slv_array_deser(mi_mfb_meta, MFB_REGIONS);

    meta_extract_g : for i in 0 to MFB_REGIONS-1 generate
    begin
        -- L3 metadata is at the beginning (highest bits): CSUM_ORIG(16) & CSUM_EN(1) & OFFSET & LENGTH
        l3_csum_orig_arr(i) <= mi_mfb_meta_arr(i)(META_WIDTH-1 downto META_WIDTH-16);
        l3_csum_en_arr(i)   <= mi_mfb_meta_arr(i)(META_WIDTH-17);
        l3_offset_arr(i)    <= mi_mfb_meta_arr(i)(META_WIDTH-18 downto META_WIDTH-18-L3_OFFSET_WIDTH+1);
        l3_length_arr(i)    <= mi_mfb_meta_arr(i)(L4_META_WIDTH+L3_LENGTH_WIDTH+PKT_LENGTH_WIDTH-1 downto L4_META_WIDTH+PKT_LENGTH_WIDTH);

        -- L4 metadata is in the middle: CSUM_ORIG(16) & CSUM_EN(1) & OFFSET & LENGTH & PROTOCOL(8) & SRC_ADDR(128) & DST_ADDR(128) & IP_VER6(1)
        l4_csum_orig_arr(i)   <= mi_mfb_meta_arr(i)(L4_META_WIDTH+PKT_LENGTH_WIDTH-1 downto L4_META_WIDTH+PKT_LENGTH_WIDTH-16);
        l4_csum_en_arr(i)     <= mi_mfb_meta_arr(i)(L4_META_WIDTH+PKT_LENGTH_WIDTH-17);
        l4_offset_arr(i)      <= mi_mfb_meta_arr(i)(L4_META_WIDTH+PKT_LENGTH_WIDTH-18 downto L4_META_WIDTH+PKT_LENGTH_WIDTH-18-L4_OFFSET_WIDTH+1);
        l4_length_arr(i)      <= mi_mfb_meta_arr(i)(L4_META_WIDTH+PKT_LENGTH_WIDTH-18-L4_OFFSET_WIDTH downto 128+128+8+1+PKT_LENGTH_WIDTH);
        l4_protocol_arr(i)    <= mi_mfb_meta_arr(i)(128+128+8+PKT_LENGTH_WIDTH downto 128+128+1+PKT_LENGTH_WIDTH);
        l4_ip_src_addr_arr(i) <= mi_mfb_meta_arr(i)(128+128+PKT_LENGTH_WIDTH downto 128+1+PKT_LENGTH_WIDTH);
        l4_ip_dst_addr_arr(i) <= mi_mfb_meta_arr(i)(128+PKT_LENGTH_WIDTH downto 1+PKT_LENGTH_WIDTH);
        l4_ip_ver6_arr(i)     <= mi_mfb_meta_arr(i)(PKT_LENGTH_WIDTH);

        -- Packet length is at the lowest bits
        l3_pkt_length_arr(i)  <= mi_mfb_meta_arr(i)(PKT_LENGTH_WIDTH-1 downto 0);
        l4_pkt_length_arr(i)  <= mi_mfb_meta_arr(i)(PKT_LENGTH_WIDTH-1 downto 0);

        -- Offset+length overflow detection for L3
        l3_offset_overflow(i) <= '1' when (resize(unsigned(l3_offset_arr(i)), PKT_LENGTH_WIDTH) + resize(unsigned(l3_length_arr(i)), PKT_LENGTH_WIDTH) > unsigned(l3_pkt_length_arr(i))) else '0';

        -- Offset+length overflow detection for L4
        l4_offset_overflow(i) <= '1' when (resize(unsigned(l4_offset_arr(i)), PKT_LENGTH_WIDTH) + resize(unsigned(l4_length_arr(i)), PKT_LENGTH_WIDTH) > unsigned(l4_pkt_length_arr(i))) else '0';

        -- Fix offset and length: disable checksum if EN='0' or offset+length > packet_length
        l3_offset_fix_arr(i) <= l3_offset_arr(i) when (l3_csum_en_arr(i) = '1' and l3_offset_overflow(i) = '0') else (others => '0');
        l3_length_fix_arr(i) <= l3_length_arr(i) when (l3_csum_en_arr(i) = '1' and l3_offset_overflow(i) = '0') else std_logic_vector(to_unsigned(1, L3_LENGTH_WIDTH));
        l4_offset_fix_arr(i) <= l4_offset_arr(i) when (l4_csum_en_arr(i) = '1' and l4_offset_overflow(i) = '0') else (others => '0');
        l4_length_fix_arr(i) <= l4_length_arr(i) when (l4_csum_en_arr(i) = '1' and l4_offset_overflow(i) = '0') else std_logic_vector(to_unsigned(1, L4_LENGTH_WIDTH));
    end generate;

    -- =========================================================================
    -- MFB_CHECKSUM_L3: Calculate L3 checksum
    -- =========================================================================

    mfb_checksum_l3_i : entity work.MFB_CHECKSUM_L3
    generic map (
        MFB_REGIONS     => MFB_REGIONS,
        MFB_REGION_SIZE => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
        PKT_MTU         => PKT_MTU,
        OFFSET_WIDTH    => L3_OFFSET_WIDTH,
        LENGTH_WIDTH    => L3_LENGTH_WIDTH,
        DEVICE          => DEVICE
    )
    port map (
        CLK                 => CLK,
        RESET               => RESET,

        RX_MFB_DATA         => dup_mfb_data0,
        RX_MFB_SOF_POS      => dup_mfb_sof_pos0,
        RX_MFB_EOF_POS      => dup_mfb_eof_pos0,
        RX_MFB_SOF          => dup_mfb_sof0,
        RX_MFB_EOF          => dup_mfb_eof0,
        RX_MFB_SRC_RDY      => dup_mfb_src_rdy0,
        RX_MFB_DST_RDY      => dup_mfb_dst_rdy0,

        RX_MFB_L3_CSUM_ORIG => slv_array_ser(l3_csum_orig_arr),
        RX_MFB_L3_CSUM_EN   => l3_csum_en_arr,
        RX_MFB_L3_OFFSET    => slv_array_ser(l3_offset_fix_arr),
        RX_MFB_L3_LENGTH    => slv_array_ser(l3_length_fix_arr),

        TX_MVB_CSUM         => l3_mvb_csum,
        TX_MVB_CSUM_OK      => l3_mvb_csum_ok,
        TX_MVB_CSUM_EN      => l3_mvb_csum_en,
        TX_MVB_VLD          => l3_mvb_vld,
        TX_MVB_SRC_RDY      => l3_mvb_src_rdy,
        TX_MVB_DST_RDY      => l3_mvb_dst_rdy
    );

    -- =========================================================================
    -- MFB_CHECKSUM_L4: Calculate L4 checksum
    -- =========================================================================

    mfb_checksum_l4_i : entity work.MFB_CHECKSUM_L4
    generic map (
        MFB_REGIONS     => MFB_REGIONS,
        MFB_REGION_SIZE => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
        PKT_MTU         => PKT_MTU,
        OFFSET_WIDTH    => L4_OFFSET_WIDTH,
        LENGTH_WIDTH    => L4_LENGTH_WIDTH,
        DEVICE          => DEVICE
    )
    port map (
        CLK                 => CLK,
        RESET               => RESET,

        RX_MFB_DATA         => dup_mfb_data1,
        RX_MFB_SOF_POS      => dup_mfb_sof_pos1,
        RX_MFB_EOF_POS      => dup_mfb_eof_pos1,
        RX_MFB_SOF          => dup_mfb_sof1,
        RX_MFB_EOF          => dup_mfb_eof1,
        RX_MFB_SRC_RDY      => dup_mfb_src_rdy1,
        RX_MFB_DST_RDY      => dup_mfb_dst_rdy1,

        RX_MFB_L4_CSUM_ORIG => slv_array_ser(l4_csum_orig_arr),
        RX_MFB_L4_CSUM_EN   => l4_csum_en_arr,
        RX_MFB_L4_OFFSET    => slv_array_ser(l4_offset_fix_arr),
        RX_MFB_L4_LENGTH    => slv_array_ser(l4_length_fix_arr),
        RX_MFB_L4_PROTOCOL  => slv_array_ser(l4_protocol_arr),
        RX_MFB_IP_SRC_ADDR  => slv_array_ser(l4_ip_src_addr_arr),
        RX_MFB_IP_DST_ADDR  => slv_array_ser(l4_ip_dst_addr_arr),
        RX_MFB_IP_VER6      => l4_ip_ver6_arr,

        TX_MVB_CSUM         => l4_mvb_csum,
        TX_MVB_CSUM_OK      => l4_mvb_csum_ok,
        TX_MVB_CSUM_EN      => l4_mvb_csum_en,
        TX_MVB_VLD          => l4_mvb_vld,
        TX_MVB_SRC_RDY      => l4_mvb_src_rdy,
        TX_MVB_DST_RDY      => l4_mvb_dst_rdy
    );

    -- =========================================================================
    -- Prepare data for MVB_MERGE_ITEMS
    -- =========================================================================

    merge_data_g : for i in 0 to MFB_REGIONS-1 generate
        -- RX0: L3 checksum results packed as CSUM(16) & OK(1) & EN(1) = 18 bits
        merge_rx0_data(i) <= l3_mvb_csum((i+1)*16-1 downto i*16) & l3_mvb_csum_ok(i) & l3_mvb_csum_en(i);
        -- RX1: L4 checksum results packed as CSUM(16) & OK(1) & EN(1) = 18 bits
        merge_rx1_data(i) <= l4_mvb_csum((i+1)*16-1 downto i*16) & l4_mvb_csum_ok(i) & l4_mvb_csum_en(i);
    end generate;

    -- =========================================================================
    -- MVB_MERGE_ITEMS: Merge L3 and L4 checksum results
    -- =========================================================================

    mvb_merge_items_i : entity work.MVB_MERGE_ITEMS
    generic map (
        RX0_ITEMS      => MFB_REGIONS,
        RX0_ITEM_WIDTH => 18,  -- 16 (CSUM) + 1 (OK) + 1 (EN)
        RX1_ITEMS      => MFB_REGIONS,
        RX1_ITEM_WIDTH => 18,  -- 16 (CSUM) + 1 (OK) + 1 (EN)
        RX0_FIFO_EN    => False,
        FIFO_DEPTH     => 32,
        OUTPUT_REG     => True,
        DEVICE         => DEVICE
    )
    port map (
        CLK         => CLK,
        RESET       => RESET,

        RX0_DATA    => slv_array_ser(merge_rx0_data),
        RX0_VLD     => l3_mvb_vld,
        RX0_SRC_RDY => l3_mvb_src_rdy,
        RX0_DST_RDY => l3_mvb_dst_rdy,

        RX1_DATA    => slv_array_ser(merge_rx1_data),
        RX1_VLD     => l4_mvb_vld,
        RX1_SRC_RDY => l4_mvb_src_rdy,
        RX1_DST_RDY => l4_mvb_dst_rdy,

        TX_DATA     => open,
        TX_DATA0    => merge_tx_data0_slv,
        TX_DATA1    => merge_tx_data1_slv,
        TX_VLD      => merge_tx_vld,
        TX_SRC_RDY  => merge_tx_src_rdy,
        TX_DST_RDY  => merge_tx_dst_rdy
    );

    -- Deserialize TX_DATA outputs
    merge_tx_data0 <= slv_array_deser(merge_tx_data0_slv, MFB_REGIONS);
    merge_tx_data1 <= slv_array_deser(merge_tx_data1_slv, MFB_REGIONS);

    -- =========================================================================
    -- Output assignment
    -- =========================================================================

    merge_tx_dst_rdy <= TX_MVB_DST_RDY;

    output_g : for i in 0 to MFB_REGIONS-1 generate
        -- L3 results from TX_DATA0: packed as CSUM(16) & OK(1) & EN(1)
        TX_MVB_L3_CSUM((i+1)*16-1 downto i*16) <= merge_tx_data0(i)(17 downto 2);
        TX_MVB_L3_CSUM_OK(i)                   <= merge_tx_data0(i)(1);
        TX_MVB_L3_CSUM_EN(i)                   <= merge_tx_data0(i)(0);

        -- L4 results from TX_DATA1: packed as CSUM(16) & OK(1) & EN(1)
        TX_MVB_L4_CSUM((i+1)*16-1 downto i*16) <= merge_tx_data1(i)(17 downto 2);
        TX_MVB_L4_CSUM_OK(i)                   <= merge_tx_data1(i)(1);
        TX_MVB_L4_CSUM_EN(i)                   <= merge_tx_data1(i)(0);
    end generate;

    TX_MVB_VLD     <= merge_tx_vld;
    TX_MVB_SRC_RDY <= merge_tx_src_rdy;

end architecture;
