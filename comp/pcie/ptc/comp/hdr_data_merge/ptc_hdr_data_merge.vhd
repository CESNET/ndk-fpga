-- ptc_hdr_data_merge.vhd: PTC header data merge
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields

entity PTC_HDR_DATA_MERGE is
    generic (
        -- =======================================================================
        -- MFB DATA BUS CONFIGURATION:
        -- =======================================================================
        -- Supported configuration is only MFB(2,1,8,32)
        MFB_REGIONS         : natural := 2;
        MFB_REGION_SIZE     : natural := 1;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 32;
        -- =======================================================================
        -- MVB HEADER BUS CONFIGURATION:
        -- =======================================================================
        -- Supported configuration is only MVB(2,128)
        MVB_ITEMS           : natural := 2;
        MVB_ITEM_WIDTH      : natural := 128;
        -- =======================================================================
        -- OTHER CONFIGURATION:
        -- =======================================================================
        -- Width of PCIe transaction size signal. Set Log2 of maximum supported
        -- PCIe transaction size (HDR + payload) in dwords
        TRANS_SIZE_WIDTH    : natural := 8;
        -- Depth of MFB FIFO (payload data)
        MFB_FIFO_DEPTH      : natural := 32;
        -- Set correct device type, is used for choose best FIFOX settings.
        DEVICE              : string  := "ULTRASCALE";
        -- Connected PCIe endpoint type ("H_TILE" or "P_TILE") (only relevant when DEVICE=="STRATIX10")
        ENDPOINT_TYPE       : string  := "H_TILE"
    );
    port (
        -- =======================================================================
        -- CLOCK AND RESET
        -- =======================================================================
        CLK                 : in  std_logic;
        RESET               : in  std_logic;
        -- =======================================================================
        -- INPUT MVB HEADER INTERFACE
        -- =======================================================================
        -- header of PCIe transaction
        RX_MVB_DATA         : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- PCIe transaction length last and first DWORD byte enable (MSB -> last byte, LSB -> first byte)
        RX_MVB_BE           : in  std_logic_vector(MVB_ITEMS*8-1 downto 0);
        -- is PCIe transaction with payload
        RX_MVB_PAYLOAD      : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        -- size of transaction payload, valid with RX_MVB_PAYLOAD
        RX_MVB_PAYLOAD_SIZE : in  std_logic_vector(MVB_ITEMS*TRANS_SIZE_WIDTH-1 downto 0);
        -- PCIe heade size type (Intel only) ('0' -> 96-bit type, '1' -> 128-bit type)
        RX_MVB_TYPE         : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        -- valid of each header of PCIe transaction in MVB word
        RX_MVB_VLD          : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        -- MVB word is valid
        RX_MVB_SRC_RDY      : in  std_logic;
        -- MVB destination is ready
        RX_MVB_DST_RDY      : out std_logic;
        -- =======================================================================
        -- INPUT MFB DATA INTERFACE CONECTED DIRECTLY TO FIFO
        -- =======================================================================
        RX_MFB_DATA         : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF_POS      : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS      : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SOF          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SRC_RDY      : in  std_logic;
        RX_MFB_DST_RDY      : out std_logic;
        -- =======================================================================
        -- OUTPUT MVB HEADER INTERFACE (only relevant for DEVICE="STRATIX10" and ENDPOINT_TYPE=="P_TILE")
        -- =======================================================================
        TX_MVB_DATA         : out std_logic_vector(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
        TX_MVB_VLD          : out std_logic_vector(MFB_REGIONS-1 downto 0);
        -- TX_MVB_SRC_RDY      : out std_logic; -- only TX_MFB_SRC_RDY is used
        -- TX_MVB_DST_RDY      : in  std_logic; -- only TX_MFB_DST_RDY is used
        -- =======================================================================
        -- OUTPUT MFB HEADER+DATA INTERFACE (for DEVICE="STRATIX10" and ENDPOINT_TYPE=="P_TILE" the HEADER is not included here)
        -- =======================================================================
        TX_MFB_DATA         : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SRC_RDY      : out std_logic;
        TX_MFB_DST_RDY      : in  std_logic;
        -- PCIe transaction length last and first DWORD byte enable (MSB -> last byte, LSB -> first byte)
        TX_MFB_BE           : out std_logic_vector(MFB_REGIONS*8-1 downto 0)
    );
end entity;

architecture FULL of PTC_HDR_DATA_MERGE is

    constant MFB_REGION_WIDTH     : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant MFB_DATA_WIDTH       : natural := MFB_REGIONS*MFB_REGION_WIDTH;
    -- Metadata of one region in TX_FIFO: TX_MVB_DATA, TX_MVB_VLD and TX_MFB_BE.
    constant TX_META_WIDTH        : natural := MVB_ITEM_WIDTH + 1 + 8;
    constant TX_FIFO_DEPTH        : natural := 16;
    -- s_dins_tx_dst_rdy is a register of not TX_FIFO_AFULL. Two more words can be written before it changes to '0'.
    constant TX_FIFO_AFULL_OFFSET : natural := 2;

    signal s_hdr_mvb_data    : std_logic_vector(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
    signal s_hdr_mvb_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal s_hdr_mfb_data    : std_logic_vector(MFB_DATA_WIDTH-1 downto 0);
    signal s_hdr_mfb_sof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal s_hdr_mfb_eof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal s_hdr_mfb_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal s_hdr_mfb_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal s_hdr_mfb_be      : std_logic_vector(MFB_REGIONS*8-1 downto 0);
    signal s_hdr_mfb_payload : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal s_hdr_mfb_type    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal s_hdr_mfb_src_rdy : std_logic;
    signal s_hdr_mfb_dst_rdy : std_logic;

    signal s_dins_tx_mvb_data    : std_logic_vector(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
    signal s_dins_tx_mvb_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal s_dins_tx_mfb_data    : std_logic_vector(MFB_DATA_WIDTH-1 downto 0);
    signal s_dins_tx_mfb_sof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal s_dins_tx_mfb_eof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal s_dins_tx_mfb_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal s_dins_tx_mfb_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal s_dins_tx_mfb_be      : std_logic_vector(MFB_REGIONS*8-1 downto 0);
    signal s_dins_tx_mfb_src_rdy : std_logic;
    signal s_dins_tx_dst_rdy     : std_logic;

    signal s_tx_fifo_wr          : std_logic;
    signal s_tx_fifo_rx_dst_rdy  : std_logic;
    signal s_tx_fifo_afull       : std_logic;
    signal s_tx_fifo_rx_meta     : slv_array_t(MFB_REGIONS-1 downto 0)(TX_META_WIDTH-1 downto 0);
    signal s_tx_fifo_tx_meta     : std_logic_vector(MFB_REGIONS*TX_META_WIDTH-1 downto 0);
    signal s_tx_fifo_tx_meta_arr : slv_array_t(MFB_REGIONS-1 downto 0)(TX_META_WIDTH-1 downto 0);
    signal s_tx_fifo_sof         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal s_tx_fifo_src_rdy     : std_logic;

begin

    -- header plan and insert
    hdr_plan_and_insert_i : entity work.PTC_HDR_DATA_MERGE_HPAI
    generic map (
        MFB_REGIONS        => MFB_REGIONS,
        MFB_REGION_SIZE    => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE     => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH     => MFB_ITEM_WIDTH,
        MVB_ITEMS          => MVB_ITEMS,
        MVB_ITEM_WIDTH     => MVB_ITEM_WIDTH,
        TRANS_SIZE_WIDTH   => TRANS_SIZE_WIDTH,
        DEVICE             => DEVICE,
        ENDPOINT_TYPE      => ENDPOINT_TYPE
    )
    port map (
        CLK                 => CLK,
        RESET               => RESET,

        RX_MVB_DATA         => RX_MVB_DATA,
        RX_MVB_BE           => RX_MVB_BE,
        RX_MVB_PAYLOAD      => RX_MVB_PAYLOAD,
        RX_MVB_PAYLOAD_SIZE => RX_MVB_PAYLOAD_SIZE,
        RX_MVB_TYPE         => RX_MVB_TYPE,
        RX_MVB_VLD          => RX_MVB_VLD,
        RX_MVB_SRC_RDY      => RX_MVB_SRC_RDY,
        RX_MVB_DST_RDY      => RX_MVB_DST_RDY,

        TX_MVB_DATA         => s_hdr_mvb_data,
        TX_MVB_VLD          => s_hdr_mvb_vld,

        TX_MFB_DATA         => s_hdr_mfb_data,
        TX_MFB_SOF_POS      => s_hdr_mfb_sof_pos,
        TX_MFB_EOF_POS      => s_hdr_mfb_eof_pos,
        TX_MFB_SOF          => s_hdr_mfb_sof,
        TX_MFB_EOF          => s_hdr_mfb_eof,
        TX_MFB_BE           => s_hdr_mfb_be,
        TX_MFB_PAYLOAD      => s_hdr_mfb_payload,
        TX_MFB_TYPE         => s_hdr_mfb_type,
        TX_MFB_SRC_RDY      => s_hdr_mfb_src_rdy,
        TX_MFB_DST_RDY      => s_hdr_mfb_dst_rdy
    );

    -- insert data
    data_insert_i : entity work.PTC_HDR_DATA_MERGE_DINS
    generic map (
        MFB_REGIONS     => MFB_REGIONS,
        MFB_REGION_SIZE => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
        MFB_FIFO_DEPTH  => MFB_FIFO_DEPTH,
        DEVICE          => DEVICE,
        ENDPOINT_TYPE   => ENDPOINT_TYPE
    )
    port map (
        CLK                 => CLK,
        RESET               => RESET,

        RX_MVB_DATA         => s_hdr_mvb_data,
        RX_MVB_VLD          => s_hdr_mvb_vld,

        RX_MFB_HDR_DATA     => s_hdr_mfb_data,
        RX_MFB_HDR_SOF_POS  => s_hdr_mfb_sof_pos,
        RX_MFB_HDR_EOF_POS  => s_hdr_mfb_eof_pos,
        RX_MFB_HDR_SOF      => s_hdr_mfb_sof,
        RX_MFB_HDR_EOF      => s_hdr_mfb_eof,
        RX_MFB_HDR_BE       => s_hdr_mfb_be,
        RX_MFB_HDR_PAYLOAD  => s_hdr_mfb_payload,
        RX_MFB_HDR_TYPE     => s_hdr_mfb_type,
        RX_MFB_HDR_SRC_RDY  => s_hdr_mfb_src_rdy,
        RX_MFB_HDR_DST_RDY  => s_hdr_mfb_dst_rdy,

        RX_MFB_DATA_DATA    => RX_MFB_DATA,
        RX_MFB_DATA_SOF_POS => RX_MFB_SOF_POS,
        RX_MFB_DATA_EOF_POS => RX_MFB_EOF_POS,
        RX_MFB_DATA_SOF     => RX_MFB_SOF,
        RX_MFB_DATA_EOF     => RX_MFB_EOF,
        RX_MFB_DATA_SRC_RDY => RX_MFB_SRC_RDY,
        RX_MFB_DATA_DST_RDY => RX_MFB_DST_RDY,

        TX_MVB_DATA         => s_dins_tx_mvb_data,
        TX_MVB_VLD          => s_dins_tx_mvb_vld,

        TX_MFB_DATA         => s_dins_tx_mfb_data,
        TX_MFB_SOF_POS      => s_dins_tx_mfb_sof_pos,
        TX_MFB_EOF_POS      => s_dins_tx_mfb_eof_pos,
        TX_MFB_SOF          => s_dins_tx_mfb_sof,
        TX_MFB_EOF          => s_dins_tx_mfb_eof,
        TX_MFB_SRC_RDY      => s_dins_tx_mfb_src_rdy,
        TX_MFB_DST_RDY      => s_dins_tx_dst_rdy,
        TX_MFB_BE           => s_dins_tx_mfb_be
    );

    -- -------------------------------------------------------------------------
    -- TX FIFO
    -- -------------------------------------------------------------------------
    -- PTC_HDR_DATA_MERGE_HPAI and PTC_HDR_DATA_MERGE_DINS use their TX_MFB_DST_RDY
    -- as the clock enable of all registers. TX_FIFO separates them from TX_MFB_DST_RDY,
    -- so they get s_dins_tx_dst_rdy from a local register.

    dins_tx_dst_rdy_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_dins_tx_dst_rdy <= '0';
            else
                s_dins_tx_dst_rdy <= not s_tx_fifo_afull;
            end if;
        end if;
    end process;

    s_tx_fifo_wr <= s_dins_tx_mfb_src_rdy and s_dins_tx_dst_rdy;

    tx_fifo_meta_g : for r in 0 to MFB_REGIONS-1 generate
        s_tx_fifo_rx_meta(r) <= s_dins_tx_mvb_data((r+1)*MVB_ITEM_WIDTH-1 downto r*MVB_ITEM_WIDTH)
                                & s_dins_tx_mvb_vld(r) & s_dins_tx_mfb_be((r+1)*8-1 downto r*8);
    end generate;

    tx_fifo_i : entity work.MFB_FIFOX
    generic map (
        REGIONS             => MFB_REGIONS,
        REGION_SIZE         => MFB_REGION_SIZE,
        BLOCK_SIZE          => MFB_BLOCK_SIZE,
        ITEM_WIDTH          => MFB_ITEM_WIDTH,
        META_WIDTH          => TX_META_WIDTH,
        FIFO_DEPTH          => TX_FIFO_DEPTH,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => TX_FIFO_AFULL_OFFSET,
        ALMOST_EMPTY_OFFSET => 0
    )
    port map (
        CLK         => CLK,
        RST         => RESET,

        RX_DATA     => s_dins_tx_mfb_data,
        RX_META     => slv_array_ser(s_tx_fifo_rx_meta,MFB_REGIONS,TX_META_WIDTH),
        RX_SOF_POS  => s_dins_tx_mfb_sof_pos,
        RX_EOF_POS  => s_dins_tx_mfb_eof_pos,
        RX_SOF      => s_dins_tx_mfb_sof,
        RX_EOF      => s_dins_tx_mfb_eof,
        RX_SRC_RDY  => s_tx_fifo_wr,
        RX_DST_RDY  => s_tx_fifo_rx_dst_rdy,

        TX_DATA     => TX_MFB_DATA,
        TX_META     => s_tx_fifo_tx_meta,
        TX_SOF_POS  => TX_MFB_SOF_POS,
        TX_EOF_POS  => TX_MFB_EOF_POS,
        TX_SOF      => s_tx_fifo_sof,
        TX_EOF      => TX_MFB_EOF,
        TX_SRC_RDY  => s_tx_fifo_src_rdy,
        TX_DST_RDY  => TX_MFB_DST_RDY,

        FIFO_STATUS => open,
        FIFO_AFULL  => s_tx_fifo_afull,
        FIFO_AEMPTY => open
    );

    -- psl tx_fifo_no_overflow :
    --      assert always ((s_tx_fifo_wr = '1') -> (s_tx_fifo_rx_dst_rdy = '1')) abort (RESET) @rising_edge(CLK)
    --      report "PTC_HDR_DATA_MERGE: TX_FIFO_AFULL_OFFSET is too small, TX_FIFO overflows!";

    -- TX_MFB_SOF and TX_MVB_VLD are '0' when TX_MFB_SRC_RDY is '0', so they are always equal.
    TX_MFB_SOF            <= s_tx_fifo_sof and (MFB_REGIONS-1 downto 0 => s_tx_fifo_src_rdy);
    TX_MFB_SRC_RDY        <= s_tx_fifo_src_rdy;
    s_tx_fifo_tx_meta_arr <= slv_array_downto_deser(s_tx_fifo_tx_meta,MFB_REGIONS,TX_META_WIDTH);

    tx_meta_unpack_g : for r in 0 to MFB_REGIONS-1 generate
        TX_MVB_DATA((r+1)*MVB_ITEM_WIDTH-1 downto r*MVB_ITEM_WIDTH) <= s_tx_fifo_tx_meta_arr(r)(TX_META_WIDTH-1 downto 1+8);
        TX_MVB_VLD(r)                                               <= s_tx_fifo_tx_meta_arr(r)(8) and s_tx_fifo_src_rdy;
        TX_MFB_BE((r+1)*8-1 downto r*8)                             <= s_tx_fifo_tx_meta_arr(r)(8-1 downto 0);
    end generate;

end architecture;
