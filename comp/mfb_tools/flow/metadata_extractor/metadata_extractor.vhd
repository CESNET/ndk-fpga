-- metadata_insertor.vhd: Metadata Insertor
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                           Description
-- ----------------------------------------------------------------------------
-- Takes Metadata from input MFB and provides them as independent output MVB.

-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------

entity METADATA_EXTRACTOR is
generic(
    -- =============================
    -- MVB characteristics
    -- =============================

    MVB_ITEMS       : integer := 2;
    -- =============================
    -- MFB characteristics
    -- =============================

    MFB_REGIONS     : integer := 2;
    MFB_REGION_SIZE : integer := 1;
    MFB_BLOCK_SIZE  : integer := 8;
    MFB_ITEM_WIDTH  : integer := 32;

    -- Width of default MFB metadata
    MFB_META_WIDTH  : integer := 0;

    -- =============================
    -- Others
    -- =============================

    -- Metadata extraction mode
    -- options:
    --     0 - Metadata from SOF Region
    --     1 - Metadata from EOF Region
    EXTRACT_MODE    : integer := 0;

    -- MVB SHAKEDOWN enables
    MVB_SHAKEDOWN_EN : boolean := True;

    -- Output PIPE enables
    OUT_MVB_PIPE_EN : boolean := false;
    OUT_MFB_PIPE_EN : boolean := false;

    -- Target device
    -- "ULTRASCALE", "7SERIES"
    DEVICE          : string  := "ULTRASCALE"
);
port(
    -- =============================
    -- Clock and Reset
    -- =============================

    CLK             : in  std_logic;
    RESET           : in  std_logic;

    -- =============================
    -- RX MFB
    -- =============================

    RX_MFB_DATA     : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    RX_MFB_META     : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
    RX_MFB_SOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_EOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_SOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    RX_MFB_EOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX_MFB_SRC_RDY  : in  std_logic;
    RX_MFB_DST_RDY  : out std_logic;

    -- =============================
    -- TX MVB
    --
    -- Extracted metadata
    -- =============================

    TX_MVB_DATA     : out std_logic_vector(MVB_ITEMS*MFB_META_WIDTH-1 downto 0);
    TX_MVB_VLD      : out std_logic_vector(MVB_ITEMS               -1 downto 0);
    TX_MVB_SRC_RDY  : out std_logic;
    TX_MVB_DST_RDY  : in  std_logic;

    -- =============================
    -- TX MFB
    -- =============================

    TX_MFB_DATA     : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- Original Metadata from RX MFB
    TX_MFB_META     : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    TX_MFB_SOF      : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_EOF      : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_SOF_POS  : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    TX_MFB_EOF_POS  : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    TX_MFB_SRC_RDY  : out std_logic;
    TX_MFB_DST_RDY  : in  std_logic

);
end entity;

architecture FULL of METADATA_EXTRACTOR is

    ---------------------------------------------------------------------------
    -- Constants
    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------
    -- Signals
    ---------------------------------------------------------------------------

    signal shake_rx_src_rdy  : std_logic;
    signal shake_rx_dst_rdy  : std_logic;

    signal shake_tx_data     : std_logic_vector(MVB_ITEMS*MFB_META_WIDTH-1 downto 0);
    signal shake_tx_vld      : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal shake_tx_next     : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal shake_tx_src_rdy  : std_logic;
    signal shake_tx_dst_rdy  : std_logic;

    signal RX_MFB_XOF         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mfb_xof_present : std_logic;

    signal pipe_mfb_src_rdy  : std_logic;
    signal pipe_mfb_dst_rdy  : std_logic;

    ---------------------------------------------------------------------------

begin

    -- -------------------------------------------------------------------------
    -- RX MFB processing
    -- -------------------------------------------------------------------------
    RX_MFB_XOF         <= RX_MFB_EOF when EXTRACT_MODE=1 else RX_MFB_SOF;
    rx_mfb_xof_present <= (or RX_MFB_XOF);

    RX_MFB_DST_RDY <= pipe_mfb_dst_rdy and (shake_rx_dst_rdy or not rx_mfb_xof_present);

    pipe_mfb_src_rdy <= RX_MFB_SRC_RDY and (shake_rx_dst_rdy or not rx_mfb_xof_present);
    shake_rx_src_rdy <= rx_mfb_xof_present and RX_MFB_SRC_RDY and pipe_mfb_dst_rdy;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- MVB Shakedown
    -- -------------------------------------------------------------------------

    mvb_shake_g: if MVB_SHAKEDOWN_EN generate
        mvb_shake_i : entity work.MVB_SHAKEDOWN
        generic map(
            RX_ITEMS    => MFB_REGIONS   ,
            TX_ITEMS    => MVB_ITEMS     ,
            ITEM_WIDTH  => MFB_META_WIDTH,
            SHAKE_PORTS => 2
        )
        port map(
            CLK        => CLK  ,
            RESET      => RESET,

            RX_DATA    => RX_MFB_META     ,
            RX_VLD     => RX_MFB_XOF      ,
            RX_SRC_RDY => shake_rx_src_rdy,
            RX_DST_RDY => shake_rx_dst_rdy,

            TX_DATA    => shake_tx_data,
            TX_VLD     => shake_tx_vld ,
            TX_NEXT    => shake_tx_next
        );

        shake_tx_next    <= (others => shake_tx_dst_rdy);
        shake_tx_src_rdy <= (or shake_tx_vld);
    else generate
        shake_tx_data    <= RX_MFB_META;
        shake_tx_vld     <= RX_MFB_XOF;
        shake_tx_src_rdy <= shake_rx_src_rdy;
        shake_rx_dst_rdy <= shake_tx_dst_rdy;
    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- TX PIPEs
    -- -------------------------------------------------------------------------

    mvb_pipe_i : entity work.MVB_PIPE
    generic map(
        ITEMS       => MVB_ITEMS     ,
        ITEM_WIDTH  => MFB_META_WIDTH,
        FAKE_PIPE   => (not OUT_MFB_PIPE_EN),
        USE_DST_RDY => true  ,
        OPT         => "SRL" ,
        DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK  ,
        RESET      => RESET,

        RX_DATA    => shake_tx_data   ,
        RX_VLD     => shake_tx_vld    ,
        RX_SRC_RDY => shake_tx_src_rdy,
        RX_DST_RDY => shake_tx_dst_rdy,

        TX_DATA    => TX_MVB_DATA   ,
        TX_VLD     => TX_MVB_VLD    ,
        TX_SRC_RDY => TX_MVB_SRC_RDY,
        TX_DST_RDY => TX_MVB_DST_RDY
    );

    mfb_pipe_i : entity work.MFB_PIPE
    generic map(
        REGIONS     => MFB_REGIONS    ,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE ,
        ITEM_WIDTH  => MFB_ITEM_WIDTH ,
        META_WIDTH  => MFB_META_WIDTH ,
        FAKE_PIPE   => (not OUT_MFB_PIPE_EN),
        USE_DST_RDY => true   ,
        PIPE_TYPE   => "SHREG",
        DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK  ,
        RESET      => RESET,

        RX_DATA    => RX_MFB_DATA   ,
        RX_META    => RX_MFB_META   ,
        RX_SOF     => RX_MFB_SOF    ,
        RX_EOF     => RX_MFB_EOF    ,
        RX_SOF_POS => RX_MFB_SOF_POS,
        RX_EOF_POS => RX_MFB_EOF_POS,
        RX_SRC_RDY => pipe_mfb_src_rdy,
        RX_DST_RDY => pipe_mfb_dst_rdy,

        TX_DATA    => TX_MFB_DATA   ,
        TX_META    => TX_MFB_META   ,
        TX_SOF     => TX_MFB_SOF    ,
        TX_EOF     => TX_MFB_EOF    ,
        TX_SOF_POS => TX_MFB_SOF_POS,
        TX_EOF_POS => TX_MFB_EOF_POS,
        TX_SRC_RDY => TX_MFB_SRC_RDY,
        TX_DST_RDY => TX_MFB_DST_RDY
    );

    -- -------------------------------------------------------------------------

end architecture;
