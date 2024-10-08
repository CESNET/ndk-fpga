-- mfb_splitter_simple_gen.vhd: MFB bus splitter with generic number of outputs
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;


-- =========================================================================
--  Description
-- =========================================================================

-- This is a 1:N MFB splitter.
-- It consists of numerous 1:2 MFB splitters in ``log2(SPLITTER_OUTPUTS)`` stages.
entity MFB_SPLITTER_SIMPLE_GEN is
    generic(
        -- Number of splitter outputs.
        SPLITTER_OUTPUTS   : integer := 8;
        -- Number of Regions in a word.
        REGIONS     : integer := 4;
        -- Number of Blocks in a Region.
        REGION_SIZE : integer := 8;
        -- Number of Items in a Block.
        BLOCK_SIZE  : integer := 8;
        -- Width  of one Item (in bits).
        ITEM_WIDTH  : integer := 8;
        -- Width of MFB metadata (in bits).
        META_WIDTH  : integer := 1;

        -- Input PIPEs enable for all 1:2 Splitters.
        -- Input registers are created when this is set to false.
        -- IN_PIPE_EN      : boolean := false;

        -- Output PIPE enable for all 1:2 Splitters.
        -- Output register are created when this is set to false.
        -- OUT_PIPE_EN     : boolean := true;

        -- FPGA device name: ULTRASCALE, STRATIX10, AGILEX, ...
        DEVICE : string := "AGILEX"
    );
    port(
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================

        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- =====================================================================
        -- RX interface
        -- =====================================================================

        -- One select bit for each stage (and for each region ofc), bit RX_MFB_SEL(0)(x) is for Stage 0, and so on.
        -- Expected to be valid with SOF!
        RX_MFB_SEL     : in  std_logic_vector(REGIONS*max(1,log2(SPLITTER_OUTPUTS))-1 downto 0);
        RX_MFB_DATA    : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        -- Valid whenever, metadata is split by words
        RX_MFB_META    : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        -- =====================================================================
        -- TX interface
        -- =====================================================================

        TX_MFB_DATA    : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        -- Valid whenever, metadata is split by words
        TX_MFB_META    : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(REGIONS*META_WIDTH-1 downto 0) := (others => (others => '0'));
        TX_MFB_SOF     : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(REGIONS-1 downto 0);
        TX_MFB_EOF     : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
        TX_MFB_DST_RDY : in  std_logic_vector(SPLITTER_OUTPUTS-1 downto 0)
    );
end entity;

architecture FULL of MFB_SPLITTER_SIMPLE_GEN is

    constant TREE_STAGES         : natural := log2(SPLITTER_OUTPUTS);
    constant SPLIT_OUTPUTS_2_POW : natural := 2**TREE_STAGES;
    --                                        MFB meta   + SEL
    constant SPLIT_META_W        : natural := META_WIDTH + max(1,TREE_STAGES);

    signal rx_mfb_meta_arr   : slv_array_t   (REGIONS            -1 downto 0)(META_WIDTH         -1 downto 0);
    signal splitter_meta_st0 : slv_array_t   (REGIONS            -1 downto 0)(SPLIT_META_W       -1 downto 0);
    signal splitter_meta     : slv_array_2d_t(TREE_STAGES+1      -1 downto 0)(SPLIT_OUTPUTS_2_POW-1 downto 0)(REGIONS*(SPLIT_META_W)-1 downto 0);
    signal splitter_meta_tmp : slv_array_3d_t(TREE_STAGES+1      -1 downto 0)(SPLIT_OUTPUTS_2_POW-1 downto 0)(REGIONS-1 downto 0)(SPLIT_META_W-1 downto 0);
    signal splitter_meta_arr : slv_array_2d_t(SPLIT_OUTPUTS_2_POW-1 downto 0)(REGIONS            -1 downto 0)(SPLIT_META_W-1 downto 0);
    signal tx_mfb_meta_arr   : slv_array_2d_t(SPLIT_OUTPUTS_2_POW-1 downto 0)(REGIONS            -1 downto 0)(META_WIDTH  -1 downto 0);
    signal rx_mfb_sel_arr    : slv_array_t   (REGIONS            -1 downto 0)(max(1,TREE_STAGES) -1 downto 0);
    signal splitter_sel      : slv_array_2d_t(TREE_STAGES+1      -1 downto 0)(SPLIT_OUTPUTS_2_POW-1 downto 0)(REGIONS-1 downto 0);
    signal splitter_data     : slv_array_2d_t(TREE_STAGES+1      -1 downto 0)(SPLIT_OUTPUTS_2_POW-1 downto 0)(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal splitter_sof      : slv_array_2d_t(TREE_STAGES+1      -1 downto 0)(SPLIT_OUTPUTS_2_POW-1 downto 0)(REGIONS-1 downto 0);
    signal splitter_eof      : slv_array_2d_t(TREE_STAGES+1      -1 downto 0)(SPLIT_OUTPUTS_2_POW-1 downto 0)(REGIONS-1 downto 0);
    signal splitter_sof_pos  : slv_array_2d_t(TREE_STAGES+1      -1 downto 0)(SPLIT_OUTPUTS_2_POW-1 downto 0)(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal splitter_eof_pos  : slv_array_2d_t(TREE_STAGES+1      -1 downto 0)(SPLIT_OUTPUTS_2_POW-1 downto 0)(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal splitter_src_rdy  : slv_array_t   (TREE_STAGES+1      -1 downto 0)(SPLIT_OUTPUTS_2_POW-1 downto 0);
    signal splitter_dst_rdy  : slv_array_t   (TREE_STAGES+1      -1 downto 0)(SPLIT_OUTPUTS_2_POW-1 downto 0);

begin

    rx_mfb_meta_arr <= slv_array_downto_deser(RX_MFB_META, REGIONS);
    rx_mfb_sel_arr  <= slv_array_downto_deser(RX_MFB_SEL , REGIONS);
    splitter_meta_g : for i in REGIONS-1 downto 0 generate
        splitter_meta_st0  (i) <= rx_mfb_meta_arr(i) & rx_mfb_sel_arr(i);
    end generate;

    splitter_data   (0)(0) <= RX_MFB_DATA;
    splitter_meta   (0)(0) <= slv_array_ser(splitter_meta_st0);
    splitter_sof    (0)(0) <= RX_MFB_SOF;
    splitter_eof    (0)(0) <= RX_MFB_EOF;
    splitter_sof_pos(0)(0) <= RX_MFB_SOF_POS;
    splitter_eof_pos(0)(0) <= RX_MFB_EOF_POS;
    splitter_src_rdy(0)(0) <= RX_MFB_SRC_RDY;

    RX_MFB_DST_RDY <= splitter_dst_rdy(0)(0);

    stage_g : for s in 0 to TREE_STAGES-1 generate
        splitter_g : for i in 0 to (2**s)-1 generate
            splitter_i: entity work.MFB_SPLITTER_SIMPLE
            generic map (
                REGIONS         => REGIONS     ,
                REGION_SIZE     => REGION_SIZE ,
                BLOCK_SIZE      => BLOCK_SIZE  ,
                ITEM_WIDTH      => ITEM_WIDTH  ,
                META_WIDTH      => SPLIT_META_W
            )
            port map (
                CLK             => CLK  ,
                RST             => RESET,

                RX_MFB_SEL      => splitter_sel    (s)(i),
                RX_MFB_DATA     => splitter_data   (s)(i),
                RX_MFB_META     => splitter_meta   (s)(i),
                RX_MFB_SOF      => splitter_sof    (s)(i),
                RX_MFB_EOF      => splitter_eof    (s)(i),
                RX_MFB_SOF_POS  => splitter_sof_pos(s)(i),
                RX_MFB_EOF_POS  => splitter_eof_pos(s)(i),
                RX_MFB_SRC_RDY  => splitter_src_rdy(s)(i),
                RX_MFB_DST_RDY  => splitter_dst_rdy(s)(i),

                TX0_MFB_DATA    => splitter_data   (s+1)(2*i),
                TX0_MFB_META    => splitter_meta   (s+1)(2*i),
                TX0_MFB_SOF     => splitter_sof    (s+1)(2*i),
                TX0_MFB_EOF     => splitter_eof    (s+1)(2*i),
                TX0_MFB_SOF_POS => splitter_sof_pos(s+1)(2*i),
                TX0_MFB_EOF_POS => splitter_eof_pos(s+1)(2*i),
                TX0_MFB_SRC_RDY => splitter_src_rdy(s+1)(2*i),
                TX0_MFB_DST_RDY => splitter_dst_rdy(s+1)(2*i),

                TX1_MFB_DATA    => splitter_data   (s+1)(2*i+1),
                TX1_MFB_META    => splitter_meta   (s+1)(2*i+1),
                TX1_MFB_SOF     => splitter_sof    (s+1)(2*i+1),
                TX1_MFB_EOF     => splitter_eof    (s+1)(2*i+1),
                TX1_MFB_SOF_POS => splitter_sof_pos(s+1)(2*i+1),
                TX1_MFB_EOF_POS => splitter_eof_pos(s+1)(2*i+1),
                TX1_MFB_SRC_RDY => splitter_src_rdy(s+1)(2*i+1),
                TX1_MFB_DST_RDY => splitter_dst_rdy(s+1)(2*i+1)
            );

            splitter_meta_tmp(s)(i) <= slv_array_downto_deser(splitter_meta(s)(i), REGIONS);
            sel_g : for j in REGIONS-1 downto 0 generate
                -- SEL bits are located at the end of this signal
                splitter_sel(s)(i)(j) <= splitter_meta_tmp(s)(i)(j)(max(1,TREE_STAGES)-s-1);
            end generate;

        end generate;

    end generate;

    outputs_g : for i in SPLITTER_OUTPUTS-1 downto 0 generate

        splitter_meta_arr(i) <= slv_array_deser(splitter_meta(TREE_STAGES)(i), REGIONS);
        tx_mfb_meta_g : for j in REGIONS-1 downto 0 generate
            tx_mfb_meta_arr(i)(j) <= splitter_meta_arr(i)(j)(SPLIT_META_W-1 downto SPLIT_META_W-META_WIDTH);
        end generate;

        TX_MFB_DATA(i)    <= splitter_data   (TREE_STAGES)(i);
        TX_MFB_META(i)    <= slv_array_ser(tx_mfb_meta_arr(i));
        TX_MFB_SOF(i)     <= splitter_sof    (TREE_STAGES)(i);
        TX_MFB_EOF(i)     <= splitter_eof    (TREE_STAGES)(i);
        TX_MFB_SOF_POS(i) <= splitter_sof_pos(TREE_STAGES)(i);
        TX_MFB_EOF_POS(i) <= splitter_eof_pos(TREE_STAGES)(i);
        TX_MFB_SRC_RDY(i) <= splitter_src_rdy(TREE_STAGES)(i);

        splitter_dst_rdy(TREE_STAGES)(i) <= TX_MFB_DST_RDY(i);

    end generate;

end architecture;
