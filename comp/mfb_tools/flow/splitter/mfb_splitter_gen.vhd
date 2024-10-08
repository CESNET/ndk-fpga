-- mfb_splitter_gen.vhd: MFB+MVB bus splitter with generic number of outputs
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                           Entity Declaration
-- ----------------------------------------------------------------------------

-- MFB+MVB bus splitter with generic number of outputs
entity MFB_SPLITTER_GEN is
    generic(
        -- number of splitter outputs
        SPLITTER_OUTPUTS : integer := 2;

        -- ===================
        -- MVB characteristics
        -- ===================

        -- number of headers
        MVB_ITEMS        : integer := 2;
        -- width of header
        MVB_ITEM_WIDTH   : integer := 32;

        -- ===================
        -- MFB characteristics
        -- ===================

        -- number of regions in word
        MFB_REGIONS      : integer := 2;
        -- number of blocks in region
        MFB_REG_SIZE     : integer := 1;
        -- number of items in block
        MFB_BLOCK_SIZE   : integer := 8;
        -- width  of one item (in bits)
        MFB_ITEM_WIDTH   : integer := 32;

        -- ===================
        -- Others
        -- ===================

        -- Size of output MVB FIFOs (in words)
        -- Minimum value is 2!
        OUTPUT_FIFO_SIZE : integer := 8;

        -- Output PIPE enable for all 2:1 splitters
        OUT_PIPE_EN     : boolean := true;

        -- "ULTRASCALE", "STRATIX10",...
        DEVICE          : string  := "ULTRASCALE"
    );
    port(
        -- ===================
        -- Common interface
        -- ===================

        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- ===================
        -- RX interfaces
        -- ===================

        RX_MVB_DATA    : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- output select for each header
        RX_MVB_SWITCH  : in  std_logic_vector(MVB_ITEMS*log2(SPLITTER_OUTPUTS)-1 downto 0);
        -- the header is associated with a payload frame on MFB
        RX_MVB_PAYLOAD : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_MVB_VLD     : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic;
        RX_MVB_DST_RDY : out std_logic;

        RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        -- ===================
        -- TX interface
        -- ===================

        TX_MVB_DATA    : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- the header is associated with a payload frame on MFB
        TX_MVB_PAYLOAD : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        TX_MVB_VLD     : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
        TX_MVB_DST_RDY : in  std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);

        TX_MFB_DATA    : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF     : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
        TX_MFB_DST_RDY : in  std_logic_vector(SPLITTER_OUTPUTS-1 downto 0)
    );
end entity;

architecture FULL of MFB_SPLITTER_GEN is

    constant TREE_STAGES : natural := log2(SPLITTER_OUTPUTS);
    constant SO_2_POW    : natural := 2**SPLITTER_OUTPUTS;

    signal s_rx_mvb_data    : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(SO_2_POW-1 downto 0)(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    signal s_rx_mvb_switch  : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(SO_2_POW-1 downto 0)(MVB_ITEMS*log2(SPLITTER_OUTPUTS)-1 downto 0);
    signal s_rx_mvb_sel     : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(SO_2_POW-1 downto 0)(MVB_ITEMS-1 downto 0) := (others => (others => (others => '0')));
    signal s_rx_mvb_payload : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(SO_2_POW-1 downto 0)(MVB_ITEMS-1 downto 0) := (others => (others => (others => '0')));
    signal s_rx_mvb_vld     : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(SO_2_POW-1 downto 0)(MVB_ITEMS-1 downto 0) := (others => (others => (others => '0')));
    signal s_rx_mvb_src_rdy : slv_array_t   (TREE_STAGES+1-1 downto 0)(SO_2_POW-1 downto 0) := (others => (others => '0'));
    signal s_rx_mvb_dst_rdy : slv_array_t   (TREE_STAGES+1-1 downto 0)(SO_2_POW-1 downto 0);
    signal s_rx_mfb_data    : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(SO_2_POW-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal s_rx_mfb_sof     : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(SO_2_POW-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal s_rx_mfb_eof     : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(SO_2_POW-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal s_rx_mfb_sof_pos : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(SO_2_POW-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal s_rx_mfb_eof_pos : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(SO_2_POW-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal s_rx_mfb_src_rdy : slv_array_t   (TREE_STAGES+1-1 downto 0)(SO_2_POW-1 downto 0);
    signal s_rx_mfb_dst_rdy : slv_array_t   (TREE_STAGES+1-1 downto 0)(SO_2_POW-1 downto 0);

begin

    s_rx_mvb_data   (0)(0) <= RX_MVB_DATA;
    s_rx_mvb_payload(0)(0) <= RX_MVB_PAYLOAD;
    s_rx_mvb_switch (0)(0) <= RX_MVB_SWITCH;
    s_rx_mvb_vld    (0)(0) <= RX_MVB_VLD;
    s_rx_mvb_src_rdy(0)(0) <= RX_MVB_SRC_RDY;
    RX_MVB_DST_RDY         <= s_rx_mvb_dst_rdy(0)(0);

    s_rx_mfb_data   (0)(0) <= RX_MFB_DATA;
    s_rx_mfb_sof    (0)(0) <= RX_MFB_SOF;
    s_rx_mfb_eof    (0)(0) <= RX_MFB_EOF;
    s_rx_mfb_sof_pos(0)(0) <= RX_MFB_SOF_POS;
    s_rx_mfb_eof_pos(0)(0) <= RX_MFB_EOF_POS;
    s_rx_mfb_src_rdy(0)(0) <= RX_MFB_SRC_RDY;
    RX_MFB_DST_RDY         <= s_rx_mfb_dst_rdy(0)(0);

    stage_g : for s in 0 to TREE_STAGES-1 generate
        splitter_g : for i in 0 to (2**s)-1 generate
            mvb_sel_g: for r in 0 to MVB_ITEMS-1 generate
                s_rx_mvb_sel(s)(i)(r) <= s_rx_mvb_switch(s)(i)(r*log2(SPLITTER_OUTPUTS)+log2(SPLITTER_OUTPUTS)-1-s);
            end generate;
            splitter_i: entity work.MFB_SPLITTER
            generic map (
                MVB_ITEMS            => MVB_ITEMS,
                MVB_META_WIDTH       => log2(SPLITTER_OUTPUTS),
                MFB_REGIONS          => MFB_REGIONS,
                MFB_REG_SIZE         => MFB_REG_SIZE,
                MFB_BLOCK_SIZE       => MFB_BLOCK_SIZE,
                MFB_ITEM_WIDTH       => MFB_ITEM_WIDTH,
                HDR_WIDTH            => MVB_ITEM_WIDTH,
                MVB_OUTPUT_FIFO_SIZE => OUTPUT_FIFO_SIZE,
                USE_OUTREG           => OUT_PIPE_EN,
                DEVICE               => DEVICE
            )
            port map (
                CLK              => CLK,
                RESET            => RESET,

                RX_MVB_HDR       => s_rx_mvb_data   (s)(i),
                RX_MVB_META      => s_rx_mvb_switch (s)(i),
                RX_MVB_SWITCH    => s_rx_mvb_sel    (s)(i),
                RX_MVB_PAYLOAD   => s_rx_mvb_payload(s)(i),
                RX_MVB_VLD       => s_rx_mvb_vld    (s)(i),
                RX_MVB_SRC_RDY   => s_rx_mvb_src_rdy(s)(i),
                RX_MVB_DST_RDY   => s_rx_mvb_dst_rdy(s)(i),
                RX_MFB_DATA      => s_rx_mfb_data   (s)(i),
                RX_MFB_SOF       => s_rx_mfb_sof    (s)(i),
                RX_MFB_EOF       => s_rx_mfb_eof    (s)(i),
                RX_MFB_SOF_POS   => s_rx_mfb_sof_pos(s)(i),
                RX_MFB_EOF_POS   => s_rx_mfb_eof_pos(s)(i),
                RX_MFB_SRC_RDY   => s_rx_mfb_src_rdy(s)(i),
                RX_MFB_DST_RDY   => s_rx_mfb_dst_rdy(s)(i),

                TX0_MVB_HDR      => s_rx_mvb_data   (s+1)(2*i),
                TX0_MVB_META     => s_rx_mvb_switch (s+1)(2*i),
                TX0_MVB_PAYLOAD  => s_rx_mvb_payload(s+1)(2*i),
                TX0_MVB_VLD      => s_rx_mvb_vld    (s+1)(2*i),
                TX0_MVB_SRC_RDY  => s_rx_mvb_src_rdy(s+1)(2*i),
                TX0_MVB_DST_RDY  => s_rx_mvb_dst_rdy(s+1)(2*i),
                TX0_MFB_DATA     => s_rx_mfb_data   (s+1)(2*i),
                TX0_MFB_SOF      => s_rx_mfb_sof    (s+1)(2*i),
                TX0_MFB_EOF      => s_rx_mfb_eof    (s+1)(2*i),
                TX0_MFB_SOF_POS  => s_rx_mfb_sof_pos(s+1)(2*i),
                TX0_MFB_EOF_POS  => s_rx_mfb_eof_pos(s+1)(2*i),
                TX0_MFB_SRC_RDY  => s_rx_mfb_src_rdy(s+1)(2*i),
                TX0_MFB_DST_RDY  => s_rx_mfb_dst_rdy(s+1)(2*i),

                TX1_MVB_HDR      => s_rx_mvb_data   (s+1)(2*i+1),
                TX1_MVB_META     => s_rx_mvb_switch (s+1)(2*i+1),
                TX1_MVB_PAYLOAD  => s_rx_mvb_payload(s+1)(2*i+1),
                TX1_MVB_VLD      => s_rx_mvb_vld    (s+1)(2*i+1),
                TX1_MVB_SRC_RDY  => s_rx_mvb_src_rdy(s+1)(2*i+1),
                TX1_MVB_DST_RDY  => s_rx_mvb_dst_rdy(s+1)(2*i+1),
                TX1_MFB_DATA     => s_rx_mfb_data   (s+1)(2*i+1),
                TX1_MFB_SOF      => s_rx_mfb_sof    (s+1)(2*i+1),
                TX1_MFB_EOF      => s_rx_mfb_eof    (s+1)(2*i+1),
                TX1_MFB_SOF_POS  => s_rx_mfb_sof_pos(s+1)(2*i+1),
                TX1_MFB_EOF_POS  => s_rx_mfb_eof_pos(s+1)(2*i+1),
                TX1_MFB_SRC_RDY  => s_rx_mfb_src_rdy(s+1)(2*i+1),
                TX1_MFB_DST_RDY  => s_rx_mfb_dst_rdy(s+1)(2*i+1)
            );
        end generate;
    end generate;

    outputs_g : for i in 0 to SPLITTER_OUTPUTS-1 generate
        TX_MVB_DATA(i)    <= s_rx_mvb_data   (TREE_STAGES)(i);
        TX_MVB_PAYLOAD(i) <= s_rx_mvb_payload(TREE_STAGES)(i);
        TX_MVB_VLD(i)     <= s_rx_mvb_vld    (TREE_STAGES)(i);
        TX_MVB_SRC_RDY(i) <= s_rx_mvb_src_rdy(TREE_STAGES)(i);
        s_rx_mvb_dst_rdy(TREE_STAGES)(i) <= TX_MVB_DST_RDY(i);

        TX_MFB_DATA(i)    <= s_rx_mfb_data   (TREE_STAGES)(i);
        TX_MFB_SOF(i)     <= s_rx_mfb_sof    (TREE_STAGES)(i);
        TX_MFB_EOF(i)     <= s_rx_mfb_eof    (TREE_STAGES)(i);
        TX_MFB_SOF_POS(i) <= s_rx_mfb_sof_pos(TREE_STAGES)(i);
        TX_MFB_EOF_POS(i) <= s_rx_mfb_eof_pos(TREE_STAGES)(i);
        TX_MFB_SRC_RDY(i) <= s_rx_mfb_src_rdy(TREE_STAGES)(i);
        s_rx_mfb_dst_rdy(TREE_STAGES)(i) <= TX_MFB_DST_RDY(i);
    end generate;

end architecture;
