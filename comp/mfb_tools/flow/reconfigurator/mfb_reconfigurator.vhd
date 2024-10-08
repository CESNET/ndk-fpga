-- mfb_reconfigurator.vhd: Implementation of MFB Reconfigurator component
-- Copyright (C) 2020 CESNET
-- Author: Jan Kubalek <kubalek@cesnet.cz>

-- SPDX-License-Identifier: BSD-3-Clause
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
-- library containing log2 function
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                                Description
-- ----------------------------------------------------------------------------
-- Changes MFB stream from one configuration to another.
-- Uses MFB components Transformer, Region Reconfigurator, Block Reconfigurator
-- and Item Reconfigurator as effectivelly as possible to achieve desired change.

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity MFB_RECONFIGURATOR is
generic(
    -- INEFFICIENCY WARNING:
    --     When increasing size of Region and/or Block, the component
    --     aligns all frames to the start of Region and eliminates
    --     any shared Regions.
    --     This can be avoided when increasing size of Blocks
    --     with all frames being larger than TX Block by setting
    --     generic FRAMES_OVER_TX_BLOCK to 1.

    -- RX MFB Configuration
    RX_REGIONS            : integer := 2;
    RX_REGION_SIZE        : integer := 2;
    RX_BLOCK_SIZE         : integer := 8;
    RX_ITEM_WIDTH         : integer := 32;

    -- TX MFB Configuration
    TX_REGIONS            : integer := 4;
    TX_REGION_SIZE        : integer := 8;
    TX_BLOCK_SIZE         : integer := 2;
    TX_ITEM_WIDTH         : integer := 8;

    META_WIDTH            : integer := 0;

    -- Metadata validity mode
    -- 0 -> with SOF
    -- 1 -> with EOF
    META_MODE             : integer := 0;

    -- Input FIFO size (in number of MFB words)
    -- Only applies when increasing size of Regions and/or Blocks
    FIFO_SIZE             : integer := 32;

    -- Frame alignment mode
    -- 1 - All frames are at least as long as on TX MFB Block
    -- 0 - Otherwise
    FRAMES_OVER_TX_BLOCK  : natural := 0;

    -- Possible optimalization for when Region size is increasing
    -- 1 - All frames are at least as long as on TX MFB Region (no FIFOX Multi needed)
    -- 0 - Otherwise
    FRAMES_OVER_TX_REGION : natural := 0;

    -- Target device
    DEVICE                : string := "ULTRASCALE"
);
port(
    CLK   : in std_logic;
    RESET : in std_logic;

    -- MFB input interface
    RX_DATA    : in  std_logic_vector(RX_REGIONS*RX_REGION_SIZE*RX_BLOCK_SIZE*RX_ITEM_WIDTH-1 downto 0);
    RX_META    : in  std_logic_vector(RX_REGIONS*META_WIDTH-1 downto 0) := (others => '0');
    RX_SOF     : in  std_logic_vector(RX_REGIONS-1 downto 0);
    RX_EOF     : in  std_logic_vector(RX_REGIONS-1 downto 0);
    RX_SOF_POS : in  std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE))-1 downto 0);
    RX_EOF_POS : in  std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE*RX_BLOCK_SIZE))-1 downto 0);
    RX_SRC_RDY : in  std_logic;
    RX_DST_RDY : out std_logic;

    -- MFB output interface
    TX_DATA    : out std_logic_vector(TX_REGIONS*TX_REGION_SIZE*TX_BLOCK_SIZE*TX_ITEM_WIDTH-1 downto 0);
    TX_META    : out std_logic_vector(TX_REGIONS*META_WIDTH-1 downto 0) := (others => '0');
    TX_SOF     : out std_logic_vector(TX_REGIONS-1 downto 0);
    TX_EOF     : out std_logic_vector(TX_REGIONS-1 downto 0);
    TX_SOF_POS : out std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE))-1 downto 0);
    TX_EOF_POS : out std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE*TX_BLOCK_SIZE))-1 downto 0);
    TX_SRC_RDY : out std_logic;
    TX_DST_RDY : in  std_logic
);
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture FULL of MFB_RECONFIGURATOR is

    constant RX_SOF_POS_W      : natural := max(1,log2(RX_REGION_SIZE));
    constant RX_EOF_POS_W      : natural := max(1,log2(RX_REGION_SIZE*RX_BLOCK_SIZE));
    constant RX_SOF_POS_TRUE_W : natural := log2(RX_REGION_SIZE);
    constant RX_EOF_POS_TRUE_W : natural := log2(RX_REGION_SIZE*RX_BLOCK_SIZE);
    constant TX_SOF_POS_W      : natural := max(1,log2(TX_REGION_SIZE));
    constant TX_EOF_POS_W      : natural := max(1,log2(TX_REGION_SIZE*TX_BLOCK_SIZE));
    constant TX_SOF_POS_TRUE_W : natural := log2(TX_REGION_SIZE);
    constant TX_EOF_POS_TRUE_W : natural := log2(TX_REGION_SIZE*TX_BLOCK_SIZE);

    constant RX_BLOCK_WIDTH    : natural := RX_ITEM_WIDTH*RX_BLOCK_SIZE;
    constant RX_REGION_WIDTH   : natural := RX_BLOCK_WIDTH*RX_REGION_SIZE;
    constant RX_WORD_WIDTH     : natural := RX_REGION_WIDTH*RX_REGIONS;
    constant TX_BLOCK_WIDTH    : natural := TX_ITEM_WIDTH*TX_BLOCK_SIZE;
    constant TX_REGION_WIDTH   : natural := TX_BLOCK_WIDTH*TX_REGION_SIZE;
    constant TX_WORD_WIDTH     : natural := TX_REGION_WIDTH*TX_REGIONS;

    constant MIN_BLOCK_WIDTH   : natural := minimum(RX_BLOCK_WIDTH ,TX_BLOCK_WIDTH );
    constant MIN_REGION_WIDTH  : natural := minimum(RX_REGION_WIDTH,TX_REGION_WIDTH);
    constant MIN_WORD_WIDTH    : natural := minimum(RX_WORD_WIDTH  ,TX_WORD_WIDTH  );

    -- Minimum MFB configuration
    constant MIN_ITEM_WIDTH    : natural := minimum(RX_ITEM_WIDTH  ,TX_ITEM_WIDTH  );
    constant MIN_BLOCK_SIZE    : natural := MIN_BLOCK_WIDTH /MIN_ITEM_WIDTH;
    constant MIN_REGION_SIZE   : natural := MIN_REGION_WIDTH/MIN_BLOCK_WIDTH;
    constant MIN_REGIONS       : natural := MIN_WORD_WIDTH  /MIN_REGION_WIDTH;

    -- ------------------------------------------------------------------------
    -- Signals
    -- ------------------------------------------------------------------------

    signal min0_data    : std_logic_vector(RX_WORD_WIDTH-1 downto 0);
    signal min0_meta    : std_logic_vector(RX_REGIONS*META_WIDTH-1 downto 0);
    signal min0_sof     : std_logic_vector(RX_REGIONS-1 downto 0);
    signal min0_eof     : std_logic_vector(RX_REGIONS-1 downto 0);
    signal min0_sof_pos : std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE))-1 downto 0);
    signal min0_eof_pos : std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE*RX_BLOCK_WIDTH/MIN_ITEM_WIDTH))-1 downto 0);
    signal min0_src_rdy : std_logic;
    signal min0_dst_rdy : std_logic;

    signal min1_data    : std_logic_vector(RX_WORD_WIDTH-1 downto 0);
    signal min1_meta    : std_logic_vector(RX_REGIONS*META_WIDTH-1 downto 0);
    signal min1_sof     : std_logic_vector(RX_REGIONS-1 downto 0);
    signal min1_eof     : std_logic_vector(RX_REGIONS-1 downto 0);
    signal min1_sof_pos : std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_WIDTH/MIN_BLOCK_WIDTH))-1 downto 0);
    signal min1_eof_pos : std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_WIDTH/MIN_BLOCK_WIDTH*MIN_BLOCK_SIZE))-1 downto 0);
    signal min1_src_rdy : std_logic;
    signal min1_dst_rdy : std_logic;

    signal min2_data    : std_logic_vector(RX_WORD_WIDTH-1 downto 0);
    signal min2_meta    : std_logic_vector(RX_WORD_WIDTH/MIN_REGION_WIDTH*META_WIDTH-1 downto 0);
    signal min2_sof     : std_logic_vector(RX_WORD_WIDTH/MIN_REGION_WIDTH-1 downto 0);
    signal min2_eof     : std_logic_vector(RX_WORD_WIDTH/MIN_REGION_WIDTH-1 downto 0);
    signal min2_sof_pos : std_logic_vector(RX_WORD_WIDTH/MIN_REGION_WIDTH*max(1,log2(MIN_REGION_SIZE))-1 downto 0);
    signal min2_eof_pos : std_logic_vector(RX_WORD_WIDTH/MIN_REGION_WIDTH*max(1,log2(MIN_REGION_SIZE*MIN_BLOCK_SIZE))-1 downto 0);
    signal min2_src_rdy : std_logic;
    signal min2_dst_rdy : std_logic;

    signal tx0_data     : std_logic_vector(TX_WORD_WIDTH-1 downto 0);
    signal tx0_meta     : std_logic_vector(TX_WORD_WIDTH/MIN_REGION_WIDTH*META_WIDTH-1 downto 0);
    signal tx0_sof      : std_logic_vector(TX_WORD_WIDTH/MIN_REGION_WIDTH-1 downto 0);
    signal tx0_eof      : std_logic_vector(TX_WORD_WIDTH/MIN_REGION_WIDTH-1 downto 0);
    signal tx0_sof_pos  : std_logic_vector(TX_WORD_WIDTH/MIN_REGION_WIDTH*max(1,log2(MIN_REGION_SIZE))-1 downto 0);
    signal tx0_eof_pos  : std_logic_vector(TX_WORD_WIDTH/MIN_REGION_WIDTH*max(1,log2(MIN_REGION_SIZE*MIN_BLOCK_SIZE))-1 downto 0);
    signal tx0_src_rdy  : std_logic;
    signal tx0_dst_rdy  : std_logic;

    signal tx1_data     : std_logic_vector(TX_WORD_WIDTH-1 downto 0);
    signal tx1_meta     : std_logic_vector(TX_REGIONS*META_WIDTH-1 downto 0);
    signal tx1_sof      : std_logic_vector(TX_REGIONS-1 downto 0);
    signal tx1_eof      : std_logic_vector(TX_REGIONS-1 downto 0);
    signal tx1_sof_pos  : std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_WIDTH/MIN_BLOCK_WIDTH))-1 downto 0);
    signal tx1_eof_pos  : std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_WIDTH/MIN_BLOCK_WIDTH*MIN_BLOCK_SIZE))-1 downto 0);
    signal tx1_src_rdy  : std_logic;
    signal tx1_dst_rdy  : std_logic;

    signal tx2_data     : std_logic_vector(TX_WORD_WIDTH-1 downto 0);
    signal tx2_meta     : std_logic_vector(TX_REGIONS*META_WIDTH-1 downto 0);
    signal tx2_sof      : std_logic_vector(TX_REGIONS-1 downto 0);
    signal tx2_eof      : std_logic_vector(TX_REGIONS-1 downto 0);
    signal tx2_sof_pos  : std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE))-1 downto 0);
    signal tx2_eof_pos  : std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE*TX_BLOCK_WIDTH/MIN_ITEM_WIDTH))-1 downto 0);
    signal tx2_src_rdy  : std_logic;
    signal tx2_dst_rdy  : std_logic;

    signal tx3_data     : std_logic_vector(TX_WORD_WIDTH-1 downto 0);
    signal tx3_meta     : std_logic_vector(TX_REGIONS*META_WIDTH-1 downto 0);
    signal tx3_sof      : std_logic_vector(TX_REGIONS-1 downto 0);
    signal tx3_eof      : std_logic_vector(TX_REGIONS-1 downto 0);
    signal tx3_sof_pos  : std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE))-1 downto 0);
    signal tx3_eof_pos  : std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE*TX_BLOCK_SIZE))-1 downto 0);
    signal tx3_src_rdy  : std_logic;
    signal tx3_dst_rdy  : std_logic;

    -- ------------------------------------------------------------------------

begin

    -- ------------------------------------------------------------------------
    -- Asserts over generics
    -- ------------------------------------------------------------------------

-- Debug print of all constants
--    assert (false)
--        report "RX_SOF_POS_W     :" & integer'image(RX_SOF_POS_W     ) & CR & LF &
--               "RX_EOF_POS_W     :" & integer'image(RX_EOF_POS_W     ) & CR & LF &
--               "RX_SOF_POS_TRUE_W:" & integer'image(RX_SOF_POS_TRUE_W) & CR & LF &
--               "RX_EOF_POS_TRUE_W:" & integer'image(RX_EOF_POS_TRUE_W) & CR & LF &
--               "TX_SOF_POS_W     :" & integer'image(TX_SOF_POS_W     ) & CR & LF &
--               "TX_EOF_POS_W     :" & integer'image(TX_EOF_POS_W     ) & CR & LF &
--               "TX_SOF_POS_TRUE_W:" & integer'image(TX_SOF_POS_TRUE_W) & CR & LF &
--               "TX_EOF_POS_TRUE_W:" & integer'image(TX_EOF_POS_TRUE_W) & CR & LF &
--               "RX_BLOCK_WIDTH   :" & integer'image(RX_BLOCK_WIDTH   ) & CR & LF &
--               "RX_REGION_WIDTH  :" & integer'image(RX_REGION_WIDTH  ) & CR & LF &
--               "RX_WORD_WIDTH    :" & integer'image(RX_WORD_WIDTH    ) & CR & LF &
--               "TX_BLOCK_WIDTH   :" & integer'image(TX_BLOCK_WIDTH   ) & CR & LF &
--               "TX_REGION_WIDTH  :" & integer'image(TX_REGION_WIDTH  ) & CR & LF &
--               "TX_WORD_WIDTH    :" & integer'image(TX_WORD_WIDTH    ) & CR & LF &
--               "MIN_BLOCK_WIDTH  :" & integer'image(MIN_BLOCK_WIDTH  ) & CR & LF &
--               "MIN_REGION_WIDTH :" & integer'image(MIN_REGION_WIDTH ) & CR & LF &
--               "MIN_WORD_WIDTH   :" & integer'image(MIN_WORD_WIDTH   ) & CR & LF &
--               "MIN_ITEM_WIDTH   :" & integer'image(MIN_ITEM_WIDTH   ) & CR & LF &
--               "MIN_BLOCK_SIZE   :" & integer'image(MIN_BLOCK_SIZE   ) & CR & LF &
--               "MIN_REGION_SIZE  :" & integer'image(MIN_REGION_SIZE  ) & CR & LF &
--               "MIN_REGIONS      :" & integer'image(MIN_REGIONS      ) severity error;

    assert (2**log2(RX_REGIONS) = RX_REGIONS and RX_REGIONS > 0)
        report "MFB_RECONFIGURATOR: RX_REGIONS must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(RX_REGION_SIZE) = RX_REGION_SIZE and RX_REGION_SIZE > 0)
        report "MFB_RECONFIGURATOR: RX_REGION_SIZE must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(RX_BLOCK_SIZE) = RX_BLOCK_SIZE and RX_BLOCK_SIZE > 0)
        report "MFB_RECONFIGURATOR: RX_BLOCK_SIZE must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(RX_ITEM_WIDTH) = RX_ITEM_WIDTH and RX_ITEM_WIDTH > 0)
        report "MFB_RECONFIGURATOR: RX_ITEM_WIDTH must be power of 2 and higher than 0."
        severity failure;

    assert (2**log2(TX_REGIONS) = TX_REGIONS and TX_REGIONS > 0)
        report "MFB_RECONFIGURATOR: TX_REGIONS must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(TX_REGION_SIZE) = TX_REGION_SIZE and TX_REGION_SIZE > 0)
        report "MFB_RECONFIGURATOR: TX_REGION_SIZE must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(TX_BLOCK_SIZE) = TX_BLOCK_SIZE and TX_BLOCK_SIZE > 0)
        report "MFB_RECONFIGURATOR: TX_BLOCK_SIZE must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(TX_ITEM_WIDTH) = TX_ITEM_WIDTH and TX_ITEM_WIDTH > 0)
        report "MFB_RECONFIGURATOR: TX_ITEM_WIDTH must be power of 2 and higher than 0."
        severity failure;

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- Convert RX MFB to have as small granularity and width as possible (and as needed)
    -- ------------------------------------------------------------------------

    rx_to_min_item_rec_i : entity work.MFB_ITEM_RECONFIGURATOR
    generic map(
        REGIONS        => RX_REGIONS                   ,
        REGION_SIZE    => RX_REGION_SIZE               ,
        RX_BLOCK_SIZE  => RX_BLOCK_SIZE                ,
        TX_BLOCK_SIZE  => RX_BLOCK_WIDTH/MIN_ITEM_WIDTH, -- Item width change
        RX_ITEM_WIDTH  => RX_ITEM_WIDTH                ,
        META_WIDTH     => META_WIDTH                   ,
        DEVICE         => DEVICE
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        RX_DATA    => RX_DATA   ,
        RX_META    => RX_META   ,
        RX_SOF     => RX_SOF    ,
        RX_EOF     => RX_EOF    ,
        RX_SOF_POS => RX_SOF_POS,
        RX_EOF_POS => RX_EOF_POS,
        RX_SRC_RDY => RX_SRC_RDY,
        RX_DST_RDY => RX_DST_RDY,

        TX_DATA    => min0_data   ,
        TX_META    => min0_meta   ,
        TX_SOF     => min0_sof    ,
        TX_EOF     => min0_eof    ,
        TX_SOF_POS => min0_sof_pos,
        TX_EOF_POS => min0_eof_pos,
        TX_SRC_RDY => min0_src_rdy,
        TX_DST_RDY => min0_dst_rdy
    );

    rx_to_min_block_rec_i : entity work.MFB_BLOCK_RECONFIGURATOR
    generic map(
        REGIONS        => RX_REGIONS                     ,
        RX_REGION_SIZE => RX_REGION_SIZE                 ,
        TX_REGION_SIZE => RX_REGION_WIDTH/MIN_BLOCK_WIDTH, -- Block width change
        RX_BLOCK_SIZE  => RX_BLOCK_WIDTH/MIN_ITEM_WIDTH  ,
        ITEM_WIDTH     => MIN_ITEM_WIDTH                 ,
        META_WIDTH     => META_WIDTH                     ,
        META_MODE      => META_MODE                      ,
        FIFO_SIZE      => FIFO_SIZE                      ,
        FRAME_ALIGN    => 0                              ,
        DEVICE         => DEVICE
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        RX_DATA    => min0_data   ,
        RX_META    => min0_meta   ,
        RX_SOF     => min0_sof    ,
        RX_EOF     => min0_eof    ,
        RX_SOF_POS => min0_sof_pos,
        RX_EOF_POS => min0_eof_pos,
        RX_SRC_RDY => min0_src_rdy,
        RX_DST_RDY => min0_dst_rdy,

        TX_DATA    => min1_data   ,
        TX_META    => min1_meta   ,
        TX_SOF     => min1_sof    ,
        TX_EOF     => min1_eof    ,
        TX_SOF_POS => min1_sof_pos,
        TX_EOF_POS => min1_eof_pos,
        TX_SRC_RDY => min1_src_rdy,
        TX_DST_RDY => min1_dst_rdy
    );

    rx_to_min_reg_rec_i : entity work.MFB_REGION_RECONFIGURATOR
    generic map(
        RX_REGIONS     => RX_REGIONS                     ,
        TX_REGIONS     => RX_WORD_WIDTH/MIN_REGION_WIDTH , -- Region width change
        RX_REGION_SIZE => RX_REGION_WIDTH/MIN_BLOCK_WIDTH,
        BLOCK_SIZE     => MIN_BLOCK_SIZE                 ,
        ITEM_WIDTH     => MIN_ITEM_WIDTH                 ,
        META_WIDTH     => META_WIDTH                     ,
        META_MODE      => META_MODE                      ,
        FIFO_SIZE      => FIFO_SIZE                      ,
        FRAME_ALIGN    => 0                              ,
        DEVICE         => DEVICE
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        RX_DATA    => min1_data   ,
        RX_META    => min1_meta   ,
        RX_SOF     => min1_sof    ,
        RX_EOF     => min1_eof    ,
        RX_SOF_POS => min1_sof_pos,
        RX_EOF_POS => min1_eof_pos,
        RX_SRC_RDY => min1_src_rdy,
        RX_DST_RDY => min1_dst_rdy,

        TX_DATA    => min2_data   ,
        TX_META    => min2_meta   ,
        TX_SOF     => min2_sof    ,
        TX_EOF     => min2_eof    ,
        TX_SOF_POS => min2_sof_pos,
        TX_EOF_POS => min2_eof_pos,
        TX_SRC_RDY => min2_src_rdy,
        TX_DST_RDY => min2_dst_rdy
    );

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- Transform word width
    -- ------------------------------------------------------------------------

    rx_to_tx_trans_i : entity work.MFB_TRANSFORMER
    generic map(
        RX_REGIONS  => RX_WORD_WIDTH/MIN_REGION_WIDTH,
        TX_REGIONS  => TX_WORD_WIDTH/MIN_REGION_WIDTH, -- Regions number change
        REGION_SIZE => MIN_REGION_SIZE               ,
        BLOCK_SIZE  => MIN_BLOCK_SIZE                ,
        ITEM_WIDTH  => MIN_ITEM_WIDTH                ,
        META_WIDTH  => META_WIDTH
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        RX_DATA    => min2_data   ,
        RX_META    => min2_meta   ,
        RX_SOP     => min2_sof    ,
        RX_EOP     => min2_eof    ,
        RX_SOP_POS => min2_sof_pos,
        RX_EOP_POS => min2_eof_pos,
        RX_SRC_RDY => min2_src_rdy,
        RX_DST_RDY => min2_dst_rdy,

        TX_DATA    => tx0_data   ,
        TX_META    => tx0_meta   ,
        TX_SOP     => tx0_sof    ,
        TX_EOP     => tx0_eof    ,
        TX_SOP_POS => tx0_sof_pos,
        TX_EOP_POS => tx0_eof_pos,
        TX_SRC_RDY => tx0_src_rdy,
        TX_DST_RDY => tx0_dst_rdy
    );

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- Convert minimalized MFB to TX MFB configuration
    -- ------------------------------------------------------------------------

    min_to_tx_reg_rec_i : entity work.MFB_REGION_RECONFIGURATOR
    generic map(
        RX_REGIONS     => TX_WORD_WIDTH/MIN_REGION_WIDTH ,
        TX_REGIONS     => TX_REGIONS                     , -- Region width change
        RX_REGION_SIZE => MIN_REGION_SIZE                ,
        BLOCK_SIZE     => MIN_BLOCK_SIZE                 ,
        ITEM_WIDTH     => MIN_ITEM_WIDTH                 ,
        META_WIDTH     => META_WIDTH                     ,
        META_MODE      => META_MODE                      ,
        FIFO_SIZE      => FIFO_SIZE                      ,
        FRAME_ALIGN    => FRAMES_OVER_TX_REGION          ,
        DEVICE         => DEVICE
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        RX_DATA    => tx0_data   ,
        RX_META    => tx0_meta   ,
        RX_SOF     => tx0_sof    ,
        RX_EOF     => tx0_eof    ,
        RX_SOF_POS => tx0_sof_pos,
        RX_EOF_POS => tx0_eof_pos,
        RX_SRC_RDY => tx0_src_rdy,
        RX_DST_RDY => tx0_dst_rdy,

        TX_DATA    => tx1_data   ,
        TX_META    => tx1_meta   ,
        TX_SOF     => tx1_sof    ,
        TX_EOF     => tx1_eof    ,
        TX_SOF_POS => tx1_sof_pos,
        TX_EOF_POS => tx1_eof_pos,
        TX_SRC_RDY => tx1_src_rdy,
        TX_DST_RDY => tx1_dst_rdy
    );

    min_to_tx_block_rec_i : entity work.MFB_BLOCK_RECONFIGURATOR
    generic map(
        REGIONS        => TX_REGIONS                     ,
        RX_REGION_SIZE => TX_REGION_WIDTH/MIN_BLOCK_WIDTH,
        TX_REGION_SIZE => TX_REGION_SIZE                 , -- Block width change
        RX_BLOCK_SIZE  => MIN_BLOCK_SIZE                 ,
        ITEM_WIDTH     => MIN_ITEM_WIDTH                 ,
        META_WIDTH     => META_WIDTH                     ,
        META_MODE      => META_MODE                      ,
        FIFO_SIZE      => FIFO_SIZE                      ,
        FRAME_ALIGN    => FRAMES_OVER_TX_BLOCK           ,
        DEVICE         => DEVICE
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        RX_DATA    => tx1_data   ,
        RX_META    => tx1_meta   ,
        RX_SOF     => tx1_sof    ,
        RX_EOF     => tx1_eof    ,
        RX_SOF_POS => tx1_sof_pos,
        RX_EOF_POS => tx1_eof_pos,
        RX_SRC_RDY => tx1_src_rdy,
        RX_DST_RDY => tx1_dst_rdy,

        TX_DATA    => tx2_data   ,
        TX_META    => tx2_meta   ,
        TX_SOF     => tx2_sof    ,
        TX_EOF     => tx2_eof    ,
        TX_SOF_POS => tx2_sof_pos,
        TX_EOF_POS => tx2_eof_pos,
        TX_SRC_RDY => tx2_src_rdy,
        TX_DST_RDY => tx2_dst_rdy
    );

    min_to_tx_item_rec_i : entity work.MFB_ITEM_RECONFIGURATOR
    generic map(
        REGIONS        => TX_REGIONS                   ,
        REGION_SIZE    => TX_REGION_SIZE               ,
        RX_BLOCK_SIZE  => TX_BLOCK_WIDTH/MIN_ITEM_WIDTH,
        TX_BLOCK_SIZE  => TX_BLOCK_SIZE                , -- Item width change
        RX_ITEM_WIDTH  => MIN_ITEM_WIDTH               ,
        META_WIDTH     => META_WIDTH                   ,
        DEVICE         => DEVICE
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        RX_DATA    => tx2_data   ,
        RX_META    => tx2_meta   ,
        RX_SOF     => tx2_sof    ,
        RX_EOF     => tx2_eof    ,
        RX_SOF_POS => tx2_sof_pos,
        RX_EOF_POS => tx2_eof_pos,
        RX_SRC_RDY => tx2_src_rdy,
        RX_DST_RDY => tx2_dst_rdy,

        TX_DATA    => tx3_data   ,
        TX_META    => tx3_meta   ,
        TX_SOF     => tx3_sof    ,
        TX_EOF     => tx3_eof    ,
        TX_SOF_POS => tx3_sof_pos,
        TX_EOF_POS => tx3_eof_pos,
        TX_SRC_RDY => tx3_src_rdy,
        TX_DST_RDY => tx3_dst_rdy
    );

    TX_DATA     <= tx3_data;
    TX_META     <= tx3_meta;
    TX_SOF      <= tx3_sof;
    TX_EOF      <= tx3_eof;
    TX_SOF_POS  <= tx3_sof_pos;
    TX_EOF_POS  <= tx3_eof_pos;
    TX_SRC_RDY  <= tx3_src_rdy;
    tx3_dst_rdy <= TX_DST_RDY;

    -- ------------------------------------------------------------------------

end architecture;
