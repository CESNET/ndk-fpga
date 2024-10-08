-- mfb_merger_simple_gen.vhd: This component is merges multiple input MFB interfaces to one.
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Vladislav Valek <valekv@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

-- This is a generic implementation of the MFB Merger when the number of input interfaces can
-- be set to arbitrary large number.
entity MFB_MERGER_SIMPLE_GEN is
    generic (
        -- number of independent input MFB interfaces, should be the power of two
        MERGER_INPUTS : natural := 2;

        -- MFB parameters
        MFB_REGIONS     : natural := 2;
        MFB_REGION_SIZE : natural := 8;
        MFB_BLOCK_SIZE  : natural := 8;
        MFB_ITEM_WIDTH  : natural := 8;
        MFB_META_WIDTH  : natural := 8;

        -- Enable masking SOF and EOF due to switch to the other input.
        MASKING_EN : boolean := TRUE;
        -- Maximum amount of clock periods with destination ready before it tries to switch to the other input.
        CNT_MAX    : integer := 64
        );
    port (
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK : in std_logic;
        RST : in std_logic;

        -- =====================================================================
        -- Multiple input RX MFB interfaces
        -- =====================================================================
        RX_MFB_DATA    : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_META    : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic_vector(MERGER_INPUTS -1 downto 0);
        RX_MFB_DST_RDY : out std_logic_vector(MERGER_INPUTS -1 downto 0);

        -- =====================================================================
        -- Single output TX interface
        -- =====================================================================
        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_META    : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
        );
end entity;

architecture FULL of MFB_MERGER_SIMPLE_GEN is
    signal mfb_data_int    : slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal mfb_meta_int    : slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal mfb_sof_int     : slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_eof_int     : slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_sof_pos_int : slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
    signal mfb_eof_pos_int : slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    signal mfb_src_rdy_int : std_logic_vector(MERGER_INPUTS -1 downto 0);
    signal mfb_dst_rdy_int : std_logic_vector(MERGER_INPUTS -1 downto 0);
begin

    mfb_data_int(0)    <= RX_MFB_DATA(0);
    mfb_meta_int(0)    <= RX_MFB_META(0);
    mfb_sof_int(0)     <= RX_MFB_SOF(0);
    mfb_eof_int(0)     <= RX_MFB_EOF(0);
    mfb_sof_pos_int(0) <= RX_MFB_SOF_POS(0);
    mfb_eof_pos_int(0) <= RX_MFB_EOF_POS(0);
    mfb_src_rdy_int(0) <= RX_MFB_SRC_RDY(0);
    RX_MFB_DST_RDY(0)  <= mfb_dst_rdy_int(0);

    mfb_merger_simple_tree_g : for i in 0 to (MERGER_INPUTS - 2) generate
        mfb_merger_simple_i : entity work.MFB_MERGER_SIMPLE
            generic map (
                REGIONS     => MFB_REGIONS,
                REGION_SIZE => MFB_REGION_SIZE,
                BLOCK_SIZE  => MFB_BLOCK_SIZE,
                ITEM_WIDTH  => MFB_ITEM_WIDTH,
                META_WIDTH  => MFB_META_WIDTH,
                MASKING_EN  => MASKING_EN,
                CNT_MAX     => CNT_MAX)
            port map (
                CLK => CLK,
                RST => RST,

                RX_MFB0_DATA    => mfb_data_int(i),
                RX_MFB0_META    => mfb_meta_int(i),
                RX_MFB0_SOF     => mfb_sof_int(i),
                RX_MFB0_SOF_POS => mfb_sof_pos_int(i),
                RX_MFB0_EOF     => mfb_eof_int(i),
                RX_MFB0_EOF_POS => mfb_eof_pos_int(i),
                RX_MFB0_SRC_RDY => mfb_src_rdy_int(i),
                RX_MFB0_DST_RDY => mfb_dst_rdy_int(i),

                RX_MFB1_DATA    => RX_MFB_DATA(i+1),
                RX_MFB1_META    => RX_MFB_META(i+1),
                RX_MFB1_SOF     => RX_MFB_SOF(i+1),
                RX_MFB1_SOF_POS => RX_MFB_SOF_POS(i+1),
                RX_MFB1_EOF     => RX_MFB_EOF(i+1),
                RX_MFB1_EOF_POS => RX_MFB_EOF_POS(i+1),
                RX_MFB1_SRC_RDY => RX_MFB_SRC_RDY(i+1),
                RX_MFB1_DST_RDY => RX_MFB_DST_RDY(i+1),

                TX_MFB_DATA    => mfb_data_int(i+1),
                TX_MFB_META    => mfb_meta_int(i+1),
                TX_MFB_SOF     => mfb_sof_int(i+1),
                TX_MFB_SOF_POS => mfb_sof_pos_int(i+1),
                TX_MFB_EOF     => mfb_eof_int(i+1),
                TX_MFB_EOF_POS => mfb_eof_pos_int(i+1),
                TX_MFB_SRC_RDY => mfb_src_rdy_int(i+1),
                TX_MFB_DST_RDY => mfb_dst_rdy_int(i+1));
    end generate;

    TX_MFB_DATA        <= mfb_data_int(mfb_data_int'high);
    TX_MFB_META        <= mfb_meta_int(mfb_meta_int'high);
    TX_MFB_SOF         <= mfb_sof_int(mfb_sof_int'high);
    TX_MFB_EOF         <= mfb_eof_int(mfb_eof_int'high);
    TX_MFB_SOF_POS     <= mfb_sof_pos_int(mfb_sof_pos_int'high);
    TX_MFB_EOF_POS     <= mfb_eof_pos_int(mfb_eof_pos_int'high);
    TX_MFB_SRC_RDY     <= mfb_src_rdy_int(mfb_src_rdy_int'high);
    mfb_dst_rdy_int(mfb_dst_rdy_int'high) <= TX_MFB_DST_RDY;
end architecture;
