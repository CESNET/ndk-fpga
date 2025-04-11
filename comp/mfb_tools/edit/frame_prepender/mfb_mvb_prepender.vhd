-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- ===========================================================================
--  Description
-- ===========================================================================

-- This component inserts MVB Items to the start of input packets.
-- One MVB Item is prepended to one MFB packet.
-- The MVB Items must be as wide as N MFB Blocks (see generic :vhdl:genconstant:`MVB_ITEM_SIZE <MFB_MVB_PREPENDER.MVB_ITEM_SIZE>`).
-- Metadata are currently not supported (see generic :vhdl:genconstant:`MFB_META_WIDTH <MFB_MVB_PREPENDER.MFB_META_WIDTH>`).
--
-- **Architecture**
--
-- MFB_MVB_PREPENDER uses MFB Extender to create space for the MVB Items (moves SOF and EOF).
-- Then it calculates a "Prepend vector", where each each bit corresponds to a MFB Block in the dataword.
-- Before the MVB Item is inserted into the dataword according to the Prepend vector,
-- it is shifted to start at SOF_POS of the current frame.
--
-- .. warning::
--
-- Does not meet timing constrains with MFB_REGIONS=4!
--
-- .. note::
--
-- Resource consumption increases with the :vhdl:genconstant:`MVB_ITEM_SIZE <MFB_MVB_PREPENDER.MVB_ITEM_SIZE>`
-- generic! (Or more precisely, with the MAX_PREPEND_REGIONS constant, which depends on this generic.)
--
entity MFB_MVB_PREPENDER is
generic(
    -- Number of Regions within a data word, must be power of 2.
    -- In this version, only one MFB Region is supported.
    MFB_REGIONS           : natural := 1;
    -- Region size (in Blocks).
    -- Values under 2 might cause unwanted behaviour.
    MFB_REGION_SIZE       : natural := 8;
    -- Block size (in Items), must be 8.
    MFB_BLOCK_SIZE        : natural := 8;
    -- Item width (in bits), must be 8.
    MFB_ITEM_WIDTH        : natural := 8;
    -- Metadata width (in bits).
    -- Currently not supported!
    -- MFB Frame Extender doesn't support standard MFB metadata, only metadata on its
    -- MVB interface (RX_MVB_USERMETA port). Metadata Extractor could be used to extract
    -- metadata on to MVB. These could be then merged with the MVB Items (from
    -- MFB Frame Length's output) going to MFB Frame Extender's RX_MVB_* interface.
    MFB_META_WIDTH        : natural := 0;

    -- Maximum size of input packets (in Items).
    -- Output packets' MTU is PKT_MTU_IN + MVB_ITEM_SIZE*MFB_BLOCK_SIZE.
    PKT_MTU_IN            : natural := 2**14;

    -- Number of MVB Items in a single word.
    MVB_ITEMS             : natural := 1;
    -- Size of each MVB Item (in MFB Blocks!).
    -- MVB Items cannot be wider than the MFB word, hence:
    -- MVB_ITEMS*MVB_ITEM_SIZE must not be greater than
    -- the number of MFB Blocks in a word (MFB_REGIONS*MFB_REGION_SIZE).
    MVB_ITEM_SIZE         : natural := 2;

    -- Number of Items (MFB words) in the Input MFB_FIFOX.
    MFB_FIFO_DEPTH        : natural := 1024;
    -- Number of Items (MVB words) in the Input MVB FIFOX.
    MVB_FIFO_DEPTH        : natural := 512;

    -- FPGA device name: ULTRASCALE, STRATIX10, AGILEX, ...
    DEVICE                : string := "AGILEX"
);
port(
    -- =======================================================================
    --  Clock and Reset
    -- =======================================================================

    CLK            : in  std_logic;
    RESET          : in  std_logic;

    -- =======================================================================
    --  RX MFB inf
    -- =======================================================================

    RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- Valid with SOF.
    RX_MFB_META    : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
    RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_SRC_RDY : in  std_logic;
    RX_MFB_DST_RDY : out std_logic;

    -- =======================================================================
    --  RX MVB inf (prepend data)
    -- =======================================================================

    RX_MVB_DATA     : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    RX_MVB_VLD      : in  std_logic_vector(MVB_ITEMS-1 downto 0);
    RX_MVB_SRC_RDY  : in  std_logic;
    RX_MVB_DST_RDY  : out std_logic;

    -- =======================================================================
    --  TX MFB inf (frames with prepended MVB data)
    -- =======================================================================

    TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- Valid with SOF.
    TX_MFB_META    : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_SRC_RDY : out std_logic;
    TX_MFB_DST_RDY : in  std_logic
);
end entity;

architecture FULL of MFB_MVB_PREPENDER is

    -- =======================================================================
    --                                CONSTANTS
    -- =======================================================================

    -- Width of a single MVB Item in a number of bits.
    constant MVB_ITEM_WIDTH     : natural := MVB_ITEM_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    -- MFB constants:
    constant WORD_WIDTH     : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant WORD_ITEMS     : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    constant WORD_BLOCKS    : natural := MFB_REGIONS*MFB_REGION_SIZE;
    constant BLOCK_WIDTH    : natural := MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant REGION_WIDTH   : natural :=             MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant SOF_POS_WIDTH  : natural := max(1,log2(MFB_REGION_SIZE));
    constant EOF_POS_WIDTH  : natural := max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));

    -- Max number of Regions a prepended Item can stretch over, no matter how shifted it is.
    -- E.g.: MFB Item with MVB_ITEM_SIZE=1 (one MFB Block) can always be only in one Region;
    --       MFB Item with MVB_ITEM_SIZE=2 can (when shifted to the last Block of the Region) continue to the next Region;
    --       MFB Item with MVB_ITEM_SIZE=10 can (when shifted to the last Block of one Region) continue through the next Region into a third one (if REGION_SIZE=8).
    constant MAX_PREPEND_REGIONS : natural := div_roundup((MVB_ITEM_SIZE-1),MFB_REGION_SIZE) + 1;
    -- Number of Blocks a single Prepend Item (including space for shifting) can occupy.
    constant PREPEND_ITEM_SIZE   : natural := MAX_PREPEND_REGIONS*MFB_REGION_SIZE;
    constant PREPEND_ITEM_WIDTH  : natural := PREPEND_ITEM_SIZE*BLOCK_WIDTH;

    -- =======================================================================
    --                                 SIGNALS
    -- =======================================================================

    signal mvb_fifoxm_din               : std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    signal mvb_fifoxm_write             : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal mvb_fifoxm_full              : std_logic;
    signal mvb_fifoxm_dout              : std_logic_vector(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
    signal mvb_fifoxm_read              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mvb_fifoxm_empty             : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal frlen_tx_data                : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal frlen_tx_sof_pos             : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal frlen_tx_eof_pos             : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal frlen_tx_sof                 : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal frlen_tx_eof                 : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal frlen_tx_src_rdy             : std_logic;
    signal frlen_tx_dst_rdy             : std_logic;
    signal frlen_tx_frlen               : std_logic_vector(MFB_REGIONS*log2(PKT_MTU_IN)-1 downto 0);

    signal MVB_ITEM_SIZE_items_arr      : u_array_t       (MFB_REGIONS-1 downto 0)(log2(PKT_MTU_IN)-1 downto 0);
    signal extd_rx_mvb_meta             : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal extd_rx_mvb_frlen            : std_logic_vector(MFB_REGIONS*log2(PKT_MTU_IN)-1 downto 0);
    signal extd_rx_mvb_ext_size         : std_logic_vector(MFB_REGIONS*log2(PKT_MTU_IN)-1 downto 0);
    signal extd_rx_mvb_vld              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal extd_rx_mvb_src_rdy          : std_logic;
    signal extd_rx_mvb_dst_rdy          : std_logic;

    signal extd_rx_mfb_data             : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal extd_rx_mfb_meta             : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal extd_rx_mfb_sof              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal extd_rx_mfb_eof              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal extd_rx_mfb_sof_pos          : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal extd_rx_mfb_eof_pos          : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal extd_rx_mfb_src_rdy          : std_logic;
    signal extd_rx_mfb_dst_rdy          : std_logic;

    signal extd_tx_mfb_data             : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal extd_tx_mfb_meta             : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal extd_tx_mfb_sof              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal extd_tx_mfb_eof              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal extd_tx_mfb_sof_pos          : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal extd_tx_mfb_eof_pos          : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal extd_tx_mfb_src_rdy          : std_logic;
    signal extd_tx_mfb_dst_rdy          : std_logic;

    signal extd_tx_sof_pos_arr          : u_array_t       (MFB_REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal extd_tx_sof_pos_word         : u_array_t       (MFB_REGIONS-1 downto 0)(max(1,log2(WORD_BLOCKS))-1 downto 0);
    signal og_sofpos_base               : u_array_t       (MFB_REGIONS-1 downto 0)(log2(WORD_BLOCKS)+1-1 downto 0);
    signal og_sofpos_in_next_word       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal og_sofpos_word               : slv_array_t     (MFB_REGIONS-1 downto 0)(max(1,log2(WORD_BLOCKS))-1 downto 0);
    signal extd_tx_sof_vld              : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal last_sof_idx                 : natural range MFB_REGIONS-1 downto 0;
    signal ends_in_this_word            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal conts_to_next_word           : std_logic;
    signal conts_to_next_word_block_0   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal conts_to_next_word_block_n   : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal conts_from_prev_word         : std_logic;
    signal og_sofpos_word_reg           : std_logic_vector(max(1,log2(WORD_BLOCKS))-1 downto 0);

    signal prepend_valid                : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal prepend_start_idx            : u_array_t       (MFB_REGIONS-1 downto 0)(max(1,log2(WORD_BLOCKS))-1 downto 0);
    signal prepend_stop_idx             : u_array_t       (MFB_REGIONS-1 downto 0)(max(1,log2(WORD_BLOCKS))-1 downto 0);
    signal prepend_blocks               : slv_array_t     (MFB_REGIONS-1 downto 0)(WORD_BLOCKS-1 downto 0);

    signal prepend_finish               : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal prepend_finish_shake         : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal last_sof_idx_reg             : natural range MFB_REGIONS-1 downto 0;
    signal prepend_shift                : u_array_t(MFB_REGIONS-1 downto 0)(max(1,log2(WORD_BLOCKS))-1 downto 0);

    signal mfb_data_reg1                : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal mfb_meta_reg1                : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal mfb_sof_pos_reg1             : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal mfb_eof_pos_reg1             : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal mfb_sof_reg1                 : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_eof_reg1                 : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_src_rdy_reg1             : std_logic;
    signal conts_from_prev_word_reg1    : std_logic;
    signal prepend_finish_reg1          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal prepend_finish_shake_reg1    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal prepend_shift_reg1           : u_array_t       (MFB_REGIONS-1 downto 0)(max(1,log2(WORD_BLOCKS))-1 downto 0);
    signal prepend_valid_reg1           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal prepend_valids_reg1          : natural range MFB_REGIONS downto 0;
    signal prepend_blocks_reg1          : std_logic_vector(WORD_BLOCKS-1 downto 0);

    signal enough_prepends              : std_logic;

    signal mvb_fifoxm_dout_arr          : u_array_t       (MFB_REGIONS-1 downto 0)(MVB_ITEM_WIDTH-1 downto 0);
    signal prepend_item_remapped        : u_array_t       (MFB_REGIONS-1 downto 0)(PREPEND_ITEM_WIDTH-1 downto 0);
    signal prepend_item_remapped_vld    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal bs_rx_data                   : slv_array_t     (MFB_REGIONS-1 downto 0)(PREPEND_ITEM_WIDTH-1 downto 0);
    signal bs_rx_sel                    : slv_array_t     (MFB_REGIONS-1 downto 0)(max(1,log2(PREPEND_ITEM_SIZE))-1 downto 0);
    signal bs_rx_src_rdy                : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal bs_rx_dst_rdy                : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal bs_tx_data                   : slv_array_t     (MFB_REGIONS-1 downto 0)(PREPEND_ITEM_WIDTH-1 downto 0);
    signal bs_tx_src_rdy                : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal bs_tx_dst_rdy                : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal mvb_prepend_region_arr       : slv_array_t     (MFB_REGIONS-1+MAX_PREPEND_REGIONS-1 downto 0)(REGION_WIDTH-1 downto 0);
    signal mvb_prepend_region_arr_overs : slv_array_t     (MAX_PREPEND_REGIONS-1-1 downto 0)(REGION_WIDTH-1 downto 0);
    signal mvb_prepend_word             : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal mvb_prepend_word_arr         : slv_array_t     (WORD_BLOCKS-1 downto 0)(BLOCK_WIDTH-1 downto 0);
    signal mfb_word_arr                 : slv_array_t     (WORD_BLOCKS-1 downto 0)(BLOCK_WIDTH-1 downto 0);
    signal prepended_data               : slv_array_t     (WORD_BLOCKS-1 downto 0)(BLOCK_WIDTH-1 downto 0);

    signal tx_dst_rdy                   : std_logic;

begin

    -- This feature could be added in the future.
    assert (MVB_ITEM_WIDTH <= WORD_WIDTH)
        report "MVB_ITEM_WIDTH = "                                 &
               integer'image(MVB_ITEM_WIDTH)                       &
               ", but must be less than or equal to WORD_WIDTH = " &
               integer'image(WORD_WIDTH)
        severity Failure;

    -- This feature could be added in the future (might not even be that complicated).
    assert MFB_META_WIDTH = 0
        report "Metadata are not currently supported! See generic's comment/documentation."
        severity Failure;

    -- =======================================================================
    -- RX FIFOs
    -- =======================================================================

    mvb_fifoxm_din   <= RX_MVB_DATA;
    mvb_fifoxm_write <= RX_MVB_VLD and RX_MVB_SRC_RDY;
    RX_MVB_DST_RDY   <= not mvb_fifoxm_full;

    mvb_fifoxm_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH          => MVB_ITEM_WIDTH,
        ITEMS               => MVB_FIFO_DEPTH,
        WRITE_PORTS         => MVB_ITEMS     ,
        READ_PORTS          => MFB_REGIONS   ,
        RAM_TYPE            => "AUTO"        ,
        DEVICE              => DEVICE        ,
        ALMOST_FULL_OFFSET  => 0             ,
        ALMOST_EMPTY_OFFSET => 0             ,
        ALLOW_SINGLE_FIFO   => True          ,
        SAFE_READ_MODE      => True
    )
    port map(
        CLK    => CLK,
        RESET  => RESET,

        DI     => mvb_fifoxm_din  ,
        WR     => mvb_fifoxm_write,
        FULL   => mvb_fifoxm_full ,
        AFULL  => open            ,

        DO     => mvb_fifoxm_dout ,
        RD     => mvb_fifoxm_read ,
        EMPTY  => mvb_fifoxm_empty,
        AEMPTY => open
    );

    -- =======================================================================
    -- MFB input logic - making space for the MVB Items
    -- =======================================================================

    -- Frame extender expects the length of each frame
    mfb_frame_length_i : entity work.MFB_FRAME_LNG
    generic map(
        REGIONS        => MFB_REGIONS     ,
        REGION_SIZE    => MFB_REGION_SIZE ,
        BLOCK_SIZE     => MFB_BLOCK_SIZE  ,
        ITEM_WIDTH     => MFB_ITEM_WIDTH  ,
        META_WIDTH     => MFB_META_WIDTH  ,
        LNG_WIDTH      => log2(PKT_MTU_IN),
        REG_BITMAP     => "111"           ,
        SATURATION     => False           ,
        IMPLEMENTATION => "parallel"
    )
    port map(
        CLK                => CLK             ,
        RESET              => RESET           ,

        RX_DATA            => RX_MFB_DATA     ,
        RX_META            => (others => '0') ,
        RX_SOF             => RX_MFB_SOF      ,
        RX_EOF             => RX_MFB_EOF      ,
        RX_SOF_POS         => RX_MFB_SOF_POS  ,
        RX_EOF_POS         => RX_MFB_EOF_POS  ,
        RX_SRC_RDY         => RX_MFB_SRC_RDY  ,
        RX_DST_RDY         => RX_MFB_DST_RDY  ,

        TX_DATA            => frlen_tx_data   ,
        TX_META            => open            ,
        TX_SOF             => frlen_tx_sof    ,
        TX_EOF             => frlen_tx_eof    ,
        TX_SOF_POS         => frlen_tx_sof_pos,
        TX_EOF_POS         => frlen_tx_eof_pos,
        TX_SRC_RDY         => frlen_tx_src_rdy,
        TX_DST_RDY         => frlen_tx_dst_rdy,

        TX_FRAME_LNG       => frlen_tx_frlen
    );

    frlen_tx_dst_rdy <= extd_rx_mvb_dst_rdy and extd_rx_mfb_dst_rdy;

    -- Frame Extender's RX_MVB_EXT_SIZE generic must be in Items
    MVB_ITEM_SIZE_items_arr <= (others => to_unsigned(MVB_ITEM_SIZE*MFB_BLOCK_SIZE, log2(PKT_MTU_IN)));

    extd_rx_mvb_meta     <= (others => '0'); -- MFB metadata could be added here (must update src_ and dst_rdy)
    extd_rx_mvb_frlen    <= frlen_tx_frlen;
    extd_rx_mvb_ext_size <= slv_array_ser(u_arr_to_slv_arr(MVB_ITEM_SIZE_items_arr));
    extd_rx_mvb_vld      <= frlen_tx_eof;
    extd_rx_mvb_src_rdy  <= frlen_tx_src_rdy and extd_rx_mfb_dst_rdy;

    extd_rx_mfb_data    <= frlen_tx_data;
    extd_rx_mfb_meta    <= (others => '0');
    extd_rx_mfb_sof     <= frlen_tx_sof;
    extd_rx_mfb_eof     <= frlen_tx_eof;
    extd_rx_mfb_sof_pos <= frlen_tx_sof_pos;
    extd_rx_mfb_eof_pos <= frlen_tx_eof_pos;
    extd_rx_mfb_src_rdy <= frlen_tx_src_rdy and extd_rx_mvb_dst_rdy;

    mfb_frame_extender_i : entity work.MFB_FRAME_EXTENDER
    generic map(
        MFB_REGIONS     => MFB_REGIONS    ,
        MFB_REGION_SIZE => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE ,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH ,
        PKT_MTU         => PKT_MTU_IN     ,
        MVB_FIFO_DEPTH  => 512            ,
        MFB_FIFO_DEPTH  => MFB_FIFO_DEPTH ,
        USERMETA_WIDTH  => 0,
        DEVICE          => DEVICE
    )
    port map(
        CLK                   => CLK  ,
        RESET                 => RESET,

        RX_MVB_USERMETA       => extd_rx_mvb_meta    ,
        RX_MVB_FRAME_LENGTH   => extd_rx_mvb_frlen   ,
        RX_MVB_EXT_SIZE       => extd_rx_mvb_ext_size,
        RX_MVB_EXT_ONLY       => (others => '0')     ,
        RX_MVB_EXT_EN         => (others => '1')     ,
        RX_MVB_VLD            => extd_rx_mvb_vld     ,
        RX_MVB_SRC_RDY        => extd_rx_mvb_src_rdy ,
        RX_MVB_DST_RDY        => extd_rx_mvb_dst_rdy ,

        RX_MFB_DATA           => extd_rx_mfb_data    ,
        RX_MFB_SOF            => extd_rx_mfb_sof     ,
        RX_MFB_EOF            => extd_rx_mfb_eof     ,
        RX_MFB_SOF_POS        => extd_rx_mfb_sof_pos ,
        RX_MFB_EOF_POS        => extd_rx_mfb_eof_pos ,
        RX_MFB_SRC_RDY        => extd_rx_mfb_src_rdy ,
        RX_MFB_DST_RDY        => extd_rx_mfb_dst_rdy ,

        TX_MVB_USERMETA       => open                ,
        TX_MVB_VLD            => open                ,
        TX_MVB_SRC_RDY        => open                ,
        TX_MVB_DST_RDY        => '1'                 ,

        TX_MFB_DATA           => extd_tx_mfb_data    ,
        TX_MFB_USERMETA       => extd_tx_mfb_meta    , -- valid with SOF
        TX_MFB_SOF            => extd_tx_mfb_sof     ,
        TX_MFB_EOF            => extd_tx_mfb_eof     ,
        TX_MFB_SOF_POS        => extd_tx_mfb_sof_pos ,
        TX_MFB_EOF_POS        => extd_tx_mfb_eof_pos ,
        TX_MFB_SRC_RDY        => extd_tx_mfb_src_rdy ,
        TX_MFB_DST_RDY        => extd_tx_mfb_dst_rdy
    );

    extd_tx_mfb_dst_rdy <= tx_dst_rdy;

    -- =======================================================================
    -- Prepend logic
    -- =======================================================================

    -- --------------------------
    --  Calculate prepend vector
    -- --------------------------
    extd_tx_sof_pos_arr <= slv_arr_to_u_arr(slv_array_deser(extd_tx_mfb_sof_pos, MFB_REGIONS));
    find_orig_sof_g : for r in 0 to MFB_REGIONS-1 generate
        -- Extend SOF POS across all Regions of the word.
        extd_tx_sof_pos_word  (r) <= r*MFB_REGION_SIZE + resize(extd_tx_sof_pos_arr(r), log2(WORD_BLOCKS));
        -- Position (base) of the original (og) SOF before extention (FRAME_EXTENDER).
        -- Add MVB_ITEM_SIZE to find out where the original frame started.
        -- One extra bit for overflow detection.
        og_sofpos_base        (r) <= resize(extd_tx_sof_pos_word(r), log2(WORD_BLOCKS)+1) + MVB_ITEM_SIZE;
        -- Wheather the original frame starts in the NEXT word is indicated by the MSB of the og_sofpos_base.
        og_sofpos_in_next_word(r) <= og_sofpos_base(r)(log2(WORD_BLOCKS));
        -- SOF POS of the original frame (across all Regions of the word)
        og_sofpos_word        (r) <= std_logic_vector(og_sofpos_base(r)(log2(WORD_BLOCKS)-1 downto 0));
    end generate;

    extd_tx_sof_vld <= extd_tx_mfb_sof and extd_tx_mfb_src_rdy;

    process(all)
    begin
        -- Index of the last Region that contains a valid SOF
        last_sof_idx <= 0;
        -- Original sofpos is somewhere in the THIS word.
        ends_in_this_word <= (others => '0');
        -- Original sofpos is somewhere in the NEXT word.
        conts_to_next_word <= '0';
        -- Original sofpos is in the next word on Block 0.
        conts_to_next_word_block_0 <= (others => '0');
        -- Original sofpos is in the next word on Block N (N /= 0).
        conts_to_next_word_block_n <= (others => '0');

        -- Finding the last SOF
        for r in 0 to MFB_REGIONS-1 loop
            if (extd_tx_sof_vld(r) = '1') then
                last_sof_idx <= r;
                if (og_sofpos_in_next_word(r) = '0') then
                    ends_in_this_word(r) <= '1';
                else
                    conts_to_next_word <= '1';
                    if ((or og_sofpos_word(r) = '0')) then
                        conts_to_next_word_block_0(r) <= '1';
                    else
                        conts_to_next_word_block_n(r) <= '1';
                    end if;
                    --exit; -- not needed because the next SOF should be moved to one of the following words by the frame_extender
                end if;
            end if;
        end loop;
    end process;

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (tx_dst_rdy = '1') then
                conts_from_prev_word <= conts_to_next_word_block_n(last_sof_idx);
                og_sofpos_word_reg   <= og_sofpos_word            (last_sof_idx);
            end if;
            if (RESET = '1') then
                conts_from_prev_word <= '0';
            end if;
        end if;
    end process;

    prepare_prepend_vector_g : for r in 0 to MFB_REGIONS-1 generate
        prepend_valid    (r) <= extd_tx_sof_vld(r) or conts_from_prev_word when (r = 0) else
                                extd_tx_sof_vld(r);

        prepend_start_idx(r) <= (others => '0')          when (r = 0) and (conts_from_prev_word = '1') else
                                extd_tx_sof_pos_word(r);

        prepend_stop_idx (r) <= unsigned(og_sofpos_word_reg)-1 when (r = 0) and (conts_from_prev_word = '1') else
                                (others => '1')                when (conts_to_next_word_block_n(r) = '1')    else
                                unsigned(og_sofpos_word(r))-1;
    end generate;

    prepend_vector_g : for r in 0 to MFB_REGIONS-1 generate
        ones_insertor_i : entity work.ONES_INSERTOR
        generic map(
            OFFSET_WIDTH => log2(WORD_BLOCKS)
        )
        port map(
            OFFSET_LOW  => prepend_start_idx(r),
            OFFSET_HIGH => prepend_stop_idx (r),
            VALID       => prepend_valid    (r),
            ONES_VECTOR => prepend_blocks   (r)
        );
    end generate;

    -- ----------------------------------
    --  Calculate prepend_finish signals
    -- ----------------------------------
    prepend_finish_g : for r in 0 to MFB_REGIONS-1 generate
        -- Indicate if the Prepend part ends here (og sofpos is in this word or the next word on Block 0).
        prepend_finish(r) <= (ends_in_this_word(r) or conts_to_next_word_block_0(r)) or conts_from_prev_word when (r=0) else
                             (ends_in_this_word(r) or conts_to_next_word_block_0(r));
    end generate;

    -- -------------
    --  A Shakedown
    -- -------------
    -- It is to correspond with MVB Items in FIFOX MULTI,
    -- which is necessary to set the mvb_fifoxm_read correctly.
    process (all)
        variable ptr : natural := 0;
    begin
        prepend_finish_shake <= (others => '0');
        ptr                  := 0;
        for r in 0 to MFB_REGIONS-1 loop
            if (prepend_finish(r) = '1') then
                prepend_finish_shake(ptr) <= '1';
                ptr                       := ptr + 1;
            end if;
        end loop;
    end process;

    -- -------------------------------
    --  First (middle) stage register
    -- -------------------------------
    process(CLK)
    begin
        if rising_edge(CLK) then
            if (tx_dst_rdy = '1') then
                mfb_data_reg1             <= extd_tx_mfb_data;
                mfb_meta_reg1             <= extd_tx_mfb_meta;
                mfb_sof_pos_reg1          <= extd_tx_mfb_sof_pos;
                mfb_eof_pos_reg1          <= extd_tx_mfb_eof_pos;
                mfb_sof_reg1              <= extd_tx_mfb_sof;
                mfb_eof_reg1              <= extd_tx_mfb_eof;
                mfb_src_rdy_reg1          <= extd_tx_mfb_src_rdy;

                conts_from_prev_word_reg1 <= conts_from_prev_word;
                prepend_finish_reg1       <= prepend_finish;
                prepend_finish_shake_reg1 <= prepend_finish_shake;
                prepend_shift_reg1        <= prepend_start_idx;
                prepend_valid_reg1        <= prepend_valid;
                prepend_valids_reg1       <= count_ones(prepend_valid);
                prepend_blocks_reg1       <= or_array(prepend_blocks);
            end if;

            if (RESET = '1') then
                mfb_src_rdy_reg1          <= '0';
                prepend_finish_reg1       <= (others => '0');
                prepend_finish_shake_reg1 <= (others => '0');
                prepend_valid_reg1        <= (others => '0');
                prepend_valids_reg1       <= 0;
            end if;
        end if;
    end process;

    enough_prepends <= '1' when count_ones(not mvb_fifoxm_empty) >= prepend_valids_reg1 else '0';

    -- -------------------
    --  Prepare MVB Items
    -- -------------------
    mvb_fifoxm_read <= tx_dst_rdy and prepend_finish_shake_reg1;

    mvb_fifoxm_dout_arr <= slv_arr_to_u_arr(slv_array_deser(mvb_fifoxm_dout, MFB_REGIONS));

    -- Mapping MVB Items to SOFs
    process(all)
        variable cnt : natural := 0;
    begin
        prepend_item_remapped     <= (others => (others => '0'));
        prepend_item_remapped_vld <= (others => '0');
        cnt                       := 0;
        for r in 0 to MFB_REGIONS-1 loop
            if (prepend_valid_reg1(r) = '1') then
                prepend_item_remapped    (r) <= resize(mvb_fifoxm_dout_arr(cnt),PREPEND_ITEM_WIDTH);
                prepend_item_remapped_vld(r) <= not mvb_fifoxm_empty(cnt);
                cnt := cnt + 1;
            end if;
        end loop;
    end process;

    -- Shift MVB Items across the word from where it will be inserted into the MFB word.
    mvb_item_shift_g : for r in 0 to MFB_REGIONS-1 generate

        bs_rx_data   (r) <= std_logic_vector(prepend_item_remapped(r));
        bs_rx_sel    (r) <= std_logic_vector(resize(prepend_shift_reg1(r)(log2(MFB_REGION_SIZE)-1 downto 0),bs_rx_sel(r)'length)); -- omit Regions
        bs_rx_src_rdy(r) <= prepend_item_remapped_vld(r);

        barrel_shifter_gen_piped_i : entity work.BARREL_SHIFTER_GEN_PIPED
        generic map(
            BLOCKS            => PREPEND_ITEM_SIZE,
            BLOCK_WIDTH       => BLOCK_WIDTH      ,
            BAR_SHIFT_LATENCY => 0                ,
            INPUT_REG         => False            ,
            OUTPUT_REG        => False            ,
            SHIFT_LEFT        => True             ,
            METADATA_WIDTH    => 0
        )
        port map(
            CLK         => CLK               ,
            RESET       => RESET             ,

            RX_DATA     => bs_rx_data     (r),
            RX_SEL      => bs_rx_sel      (r),
            RX_METADATA => (others => '0')   ,
            RX_SRC_RDY  => bs_rx_src_rdy  (r),
            RX_DST_RDY  => open              ,

            TX_DATA     => bs_tx_data     (r),
            TX_METADATA => open              ,
            TX_SRC_RDY  => bs_tx_src_rdy  (r),
            TX_DST_RDY  => bs_tx_dst_rdy  (r)
        );
    end generate;
    bs_tx_dst_rdy <= tx_dst_rdy and prepend_finish_reg1;

    -- "Chain" the shifted MVB Items together into a single word.
    -- The thought behind this logic is that:
    --  - we expect all frames to be at least 64B (>56B) so only one "prepend" to occur in one Region;
    --  - MVB Items are extended to as many Regions as are needed to never roll over even after the maximum shift (see MAX_PREPEND_REGIONS);
    --  - SOFs should be spaced out accordingly to the size of the prepended MVB Items (see the Mapping process);
    --  - due to this, we can insert MVB Items into the final mvb_prepend_word "over each other" but they will never collide;
    --
    -- This insertion might not be very effective and could be optimized (perhaps by ORing the Items?).
    process(all)
    begin
        mvb_prepend_region_arr <= (others => (others => '0'));
        -- Select a new Prepend Item or use the leftovers from the previous word for Region 0.
        if (conts_from_prev_word_reg1 = '1') then
            -- There is one less Region when using the leftovers.
            mvb_prepend_region_arr(MAX_PREPEND_REGIONS-1-1 downto 0) <= mvb_prepend_region_arr_overs;
        else
            mvb_prepend_region_arr(MAX_PREPEND_REGIONS  -1 downto 0) <= slv_array_deser(bs_tx_data(0),MAX_PREPEND_REGIONS);
        end if;
        -- For all other Regions, use a new Prepend Item.
        for r in 1 to MFB_REGIONS-1 loop
            if (bs_tx_src_rdy(r) = '1') then
                mvb_prepend_region_arr(r+MAX_PREPEND_REGIONS-1 downto r) <= slv_array_deser(bs_tx_data(r),MAX_PREPEND_REGIONS);
            end if;
        end loop;
    end process;

    mvb_prepend_word <= slv_array_ser(mvb_prepend_region_arr(MFB_REGIONS-1 downto 0));

    -- Store overflowed Regions to be (potentionally) used in the next word.
    process(CLK)
    begin
        if rising_edge(CLK) then
            if (tx_dst_rdy = '1') then
                mvb_prepend_region_arr_overs <= mvb_prepend_region_arr(mvb_prepend_region_arr'high downto MFB_REGIONS);
            end if;
            if (RESET = '1') then
                mvb_prepend_region_arr_overs <= (others => (others => '0'));
            end if;
        end if;
    end process;

    -- =======================================================================
    -- Data insertion
    -- =======================================================================

    mvb_prepend_word_arr <= slv_array_deser(mvb_prepend_word, WORD_BLOCKS);
    mfb_word_arr         <= slv_array_deser(mfb_data_reg1, WORD_BLOCKS);
    prepend_data_g : for b in 0 to WORD_BLOCKS-1 generate
        prepended_data(b) <= mvb_prepend_word_arr(b) when (prepend_blocks_reg1(b) = '1') else mfb_word_arr(b);
    end generate;

    -- =======================================================================
    -- Output register
    -- =======================================================================

    tx_dst_rdy <= TX_MFB_DST_RDY and enough_prepends;

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (TX_MFB_DST_RDY = '1') then
                TX_MFB_DATA    <= slv_array_ser(prepended_data);
                TX_MFB_META    <= mfb_meta_reg1;
                TX_MFB_SOF_POS <= mfb_sof_pos_reg1;
                TX_MFB_EOF_POS <= mfb_eof_pos_reg1;
                TX_MFB_SOF     <= mfb_sof_reg1;
                TX_MFB_EOF     <= mfb_eof_reg1;
                TX_MFB_SRC_RDY <= mfb_src_rdy_reg1 and enough_prepends;
            end if;
            if (RESET = '1') then
                TX_MFB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

end architecture;
