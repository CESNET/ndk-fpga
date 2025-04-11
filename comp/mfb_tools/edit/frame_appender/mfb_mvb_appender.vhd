-- Copyright (C) 2024 CESNET z. s. p. o.
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

-- This component appends input MVB Items to packets (moves EOF).
-- Its simple architecture utilizes MFB reconfigurators:
-- Input MFB words are first reconfigured to MFB#(1,1,MFB_REGION_SIZE*MFB_BLOCK_SIZE,MFB_ITEM_WIDTH),
-- so SOFs are aligned to the start of word (MFB Block 0).
-- The appending process occurs in two steps:
--
-- #. MVB append data are inserted onto a (temporary) MFB word and
--    shifted according to the EOF (POS) of the original packet.
-- #. This word is multiplexed with the MFB word containing the original packet
--    according to the so-called "append vector", which contains 1s from
--    the EOF of the original packet to the offset created by the append data.
--
-- .. warning::
--     In this first version, the component has certain limitations:
--
--     1) Only one MFB Region is supported.
--        Multiple MFB Reagions are difficult to handle for the shifting mechanism.
--     2) MVB Items cannot be wider than the MFB word.
--        This would also cause problems for the shifting mechanism.
--
-- Further versions could remove these limitations.
-- They could also utilize MFB Frame Masker instead of the Reconfigurators.
--
entity MFB_MVB_APPENDER is
generic(
    -- Number of Regions within a data word, must be power of 2.
    -- In this version, only one MFB Region is supported.
    MFB_REGIONS           : natural := 1;
    -- Region size (in Blocks).
    MFB_REGION_SIZE       : natural := 8;
    -- Block size (in Items), must be 8.
    MFB_BLOCK_SIZE        : natural := 8;
    -- Item width (in bits), must be 8.
    MFB_ITEM_WIDTH        : natural := 8;
    -- Metadata width (in bits).
    MFB_META_WIDTH        : natural := 0;

    -- Maximum size of input packets (in Items).
    -- Output packets' MTU is PKT_MTU_IN + MVB_ITEM_SIZE.
    PKT_MTU_IN            : natural := 2**14;

    -- Number of MVB Items in one word.
    MVB_ITEMS             : natural := 1;
    -- Size of each MVB Item (in MFB Items!).
    -- MVB_ITEMS*MVB_ITEM_SIZE must not be greater than
    -- the number of MFB Items in a word (MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE).
    MVB_ITEM_SIZE         : natural := 16;

    -- Number of Items in the Input MFB_FIFOX.
    MFB_FIFO_DEPTH        : natural := 32;
    -- Number of Items in the Input APPEND FIFOX.
    APPEND_FIFO_DEPTH     : natural := 32;

    -- Whether the input and output MFB configurations are the same.
    -- If "false", TX MFB configuration is 1,1,MFB_REGION_SIZE*MFB_BLOCK_SIZE,MFB_ITEM_WIDTH.
    -- Disabling backward configuration saves resources.
    RX_MFB_CONF_EQ_TX     : boolean := True;

    -- FPGA device name: ULTRASCALE, STRATIX10, AGILEX, ...
    DEVICE                : string := "STRATIX10"
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
    --  RX MVB inf (append data)
    -- =======================================================================

    RX_MVB_DATA     : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    RX_MVB_VLD      : in  std_logic_vector(MVB_ITEMS-1 downto 0);
    RX_MVB_SRC_RDY  : in  std_logic;
    RX_MVB_DST_RDY  : out std_logic;

    -- =======================================================================
    --  TX MFB inf (frames with appended MVB data)
    -- =======================================================================

    TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- Valid with SOF.
    TX_MFB_META    : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(tsel(RX_MFB_CONF_EQ_TX, MFB_REGION_SIZE, 1)))-1 downto 0);
    TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_SRC_RDY : out std_logic;
    TX_MFB_DST_RDY : in  std_logic
);
end entity;

architecture FULL of MFB_MVB_APPENDER is

    -- =======================================================================
    --                                CONSTANTS
    -- =======================================================================

    constant WORD_WIDTH     : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant REGION_WIDTH   : natural :=             MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant REGION_ITEMS   : natural :=             MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    constant WORD_ITEMS     : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    constant SOF_POS_WIDTH  : natural := max(1,log2(MFB_REGION_SIZE));
    constant EOF_POS_WIDTH  : natural := max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));

    constant MVB_ITEM_WIDTH : natural := MVB_ITEM_SIZE*MFB_ITEM_WIDTH;
    constant OFFSET_WIDTH   : natural := log2(PKT_MTU_IN+MVB_ITEM_SIZE);
    -- Maximum amount of Words a single packet can stretch over. (multiplied by 2 for one extra bit)
    constant PKT_MAX_WORDS  : natural := div_roundup(PKT_MTU_IN+MVB_ITEM_SIZE, MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE) * 2;

    -- =======================================================================
    --                                 SIGNALS
    -- =======================================================================

    signal mvb_fifoxm_din               : std_logic_vector(MVB_ITEM_WIDTH-1 downto 0);
    signal mvb_fifoxm_write             : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal mvb_fifoxm_full              : std_logic;

    signal mvb_fifoxm_dout              : std_logic_vector(MVB_ITEM_WIDTH-1 downto 0);
    signal mvb_fifoxm_read              : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal mvb_fifoxm_empty             : std_logic_vector(MVB_ITEMS-1 downto 0);

    signal mfb_fifox_data               : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal mfb_fifox_meta               : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal mfb_fifox_sof_pos            : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal mfb_fifox_eof_pos            : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal mfb_fifox_sof                : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_fifox_eof                : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_fifox_src_rdy            : std_logic;
    signal mfb_fifox_dst_rdy            : std_logic;

    signal mfb_reconf_tx_data           : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal mfb_reconf_tx_meta           : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal mfb_reconf_tx_sof_pos        : std_logic_vector(MFB_REGIONS*1-1 downto 0);
    signal mfb_reconf_tx_eof_pos        : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal mfb_reconf_tx_sof            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_reconf_tx_eof            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_reconf_tx_src_rdy        : std_logic;
    signal mfb_reconf_tx_dst_rdy        : std_logic;

    signal mfb_reconf_tx_eof_appeared   : std_logic;

    signal mfb_reconf_tx_eof_pos_arr    : slv_array_t     (MFB_REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal new_eofpos_offset            : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    signal word_cnt                     : u_array_t       (MFB_REGIONS downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);
    signal new_eofpos_offset_vld        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal new_eofpos_offset_vld_reg    : std_logic;
    signal new_eof_pos                  : u_array_t       (MFB_REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal new_eof                      : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal append_start_item_idx        : unsigned(EOF_POS_WIDTH+1-1 downto 0);
    signal append_end_item_idx          : unsigned(EOF_POS_WIDTH-1 downto 0);
    signal append_begins_here           : std_logic;
    signal append_ends_here             : std_logic;
    signal offset_lo                    : unsigned(log2(REGION_ITEMS)-1 downto 0);
    signal offset_hi                    : unsigned(log2(REGION_ITEMS)-1 downto 0);
    signal offset_vld                   : std_logic;
    signal append_vec                   : std_logic_vector(REGION_ITEMS-1 downto 0);

    signal mfb_data_reg1                : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal mfb_meta_reg1                : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal mfb_sof_pos_reg1             : std_logic_vector(MFB_REGIONS*1-1 downto 0);
    signal mfb_eof_pos_reg1             : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal mfb_sof_reg1                 : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_eof_reg1                 : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_old_eof_reg1             : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_src_rdy_reg1             : std_logic;
    signal append_begins_here_reg1      : std_logic;
    signal append_ends_here_reg1        : std_logic;
    signal append_vld_reg1              : std_logic;
    signal append_shift_reg1            : std_logic_vector(EOF_POS_WIDTH-1 downto 0);
    signal append_vec_reg1              : std_logic_vector(REGION_ITEMS-1 downto 0);

    signal bs_rx_data                   : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal bs_rx_sel                    : std_logic_vector(EOF_POS_WIDTH-1 downto 0);
    signal bs_rx_src_rdy                : std_logic;
    signal bs_tx_data                   : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal bs_tx_src_rdy                : std_logic;
    signal bs_tx_dst_rdy                : std_logic;

    signal mfb_data_items_arr           : slv_array_t(WORD_ITEMS-1 downto 0)(MFB_ITEM_WIDTH-1 downto 0);
    signal append_data_items_arr        : slv_array_t(WORD_ITEMS-1 downto 0)(MFB_ITEM_WIDTH-1 downto 0);
    signal mfb_data_appended_arr        : slv_array_t(WORD_ITEMS-1 downto 0)(MFB_ITEM_WIDTH-1 downto 0);

    signal dst_rdy                      : std_logic;
    signal mfb_src_rdy_appended         : std_logic;
    signal mfb_dst_rdy                  : std_logic;

begin

    -- This feature could be added in the future.
    -- The biggest problem is shifting such a large amount of data.
    assert (MVB_ITEM_WIDTH <= WORD_WIDTH)
        report "MVB_ITEM_WIDTH = "                                 &
               integer'image(MVB_ITEM_WIDTH)                       &
               ", but must be less than or equal to WORD_WIDTH = " &
               integer'image(WORD_WIDTH)
        severity Failure;

    assert (MFB_REGIONS = 1)
        report "MFB_REGIONS = " & integer'image(MFB_REGIONS) & ", but must be 1!"
        severity Failure;

    -- =======================================================================
    -- RX FIFOs
    -- =======================================================================

    mvb_fifoxm_din   <= RX_MVB_DATA;
    mvb_fifoxm_write <= RX_MVB_VLD and RX_MVB_SRC_RDY;
    RX_MVB_DST_RDY   <= not mvb_fifoxm_full;

    mvb_fifoxm_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH          => MVB_ITEM_WIDTH   ,
        ITEMS               => APPEND_FIFO_DEPTH,
        WRITE_PORTS         => MVB_ITEMS        ,
        READ_PORTS          => 1                ,
        RAM_TYPE            => "AUTO"           ,
        DEVICE              => DEVICE           ,
        ALMOST_FULL_OFFSET  => 0                ,
        ALMOST_EMPTY_OFFSET => 0                ,
        ALLOW_SINGLE_FIFO   => True             ,
        SAFE_READ_MODE      => False
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

    mvb_fifoxm_read(0) <= append_ends_here_reg1 and mfb_src_rdy_reg1 and TX_MFB_DST_RDY and not mvb_fifoxm_empty(0);

    -- Using MFB Reconfigurator simplifies the appending logic, however, it also reduces throughput.
    -- Hence, this is expected to be only a temporary solution.
    -- This FIFO is left here for a future full-throughput solution (Hint: use also Frame Masker?).
    -- mfb_fifox_i : entity work.MFB_FIFOX
    -- generic map(
    --     REGIONS             => MFB_REGIONS    ,
    --     REGION_SIZE         => MFB_REGION_SIZE,
    --     BLOCK_SIZE          => MFB_BLOCK_SIZE ,
    --     ITEM_WIDTH          => MFB_ITEM_WIDTH ,
    --     META_WIDTH          => MFB_META_WIDTH ,
    --     FIFO_DEPTH          => MFB_FIFO_DEPTH ,
    --     RAM_TYPE            => "AUTO"         ,
    --     DEVICE              => DEVICE         ,
    --     ALMOST_FULL_OFFSET  => 0              ,
    --     ALMOST_EMPTY_OFFSET => 0
    -- )
    -- port map(
    --     CLK => CLK,
    --     RST => RESET,

    --     RX_DATA     => RX_MFB_DATA      ,
    --     RX_META     => RX_MFB_META      ,
    --     RX_SOF_POS  => RX_MFB_SOF_POS   ,
    --     RX_EOF_POS  => RX_MFB_EOF_POS   ,
    --     RX_SOF      => RX_MFB_SOF       ,
    --     RX_EOF      => RX_MFB_EOF       ,
    --     RX_SRC_RDY  => RX_MFB_SRC_RDY   ,
    --     RX_DST_RDY  => RX_MFB_DST_RDY   ,

    --     TX_DATA     => mfb_fifox_data   ,
    --     TX_META     => mfb_fifox_meta   ,
    --     TX_SOF_POS  => mfb_fifox_sof_pos,
    --     TX_EOF_POS  => mfb_fifox_eof_pos,
    --     TX_SOF      => mfb_fifox_sof    ,
    --     TX_EOF      => mfb_fifox_eof    ,
    --     TX_SRC_RDY  => mfb_fifox_src_rdy,
    --     TX_DST_RDY  => mfb_fifox_dst_rdy,

    --     FIFO_STATUS => open             ,
    --     FIFO_AFULL  => open             ,
    --     FIFO_AEMPTY => open
    -- );

    -- =======================================================================
    -- Logic to serch for new EOF(POS) and using it to create a vector
    -- with '1's from the "old" EOF_POS to the "new" EOF_POS.
    -- =======================================================================

    mfb_reconf_in_i : entity work.MFB_RECONFIGURATOR
    generic map(
        RX_REGIONS            => MFB_REGIONS                   ,
        RX_REGION_SIZE        => MFB_REGION_SIZE               ,
        RX_BLOCK_SIZE         => MFB_BLOCK_SIZE                ,
        RX_ITEM_WIDTH         => MFB_ITEM_WIDTH                ,
        TX_REGIONS            => 1                             ,
        TX_REGION_SIZE        => 1                             ,
        TX_BLOCK_SIZE         => MFB_REGION_SIZE*MFB_BLOCK_SIZE,
        TX_ITEM_WIDTH         => MFB_ITEM_WIDTH                ,
        META_WIDTH            => MFB_META_WIDTH                ,
        META_MODE             => 0                             ,
        FIFO_SIZE             => MFB_FIFO_DEPTH                ,
        FRAMES_OVER_TX_BLOCK  => 0                             ,
        FRAMES_OVER_TX_REGION => 0                             ,
        DEVICE                => DEVICE
    )
    port map(
        CLK                 => CLK                  ,
        RESET               => RESET                ,

        RX_DATA             => RX_MFB_DATA          ,
        RX_META             => RX_MFB_META          ,
        RX_SOF_POS          => RX_MFB_SOF_POS       ,
        RX_EOF_POS          => RX_MFB_EOF_POS       ,
        RX_SOF              => RX_MFB_SOF           ,
        RX_EOF              => RX_MFB_EOF           ,
        RX_SRC_RDY          => RX_MFB_SRC_RDY       ,
        RX_DST_RDY          => RX_MFB_DST_RDY       ,

        TX_DATA             => mfb_reconf_tx_data   ,
        TX_META             => mfb_reconf_tx_meta   ,
        TX_SOF_POS          => mfb_reconf_tx_sof_pos,
        TX_EOF_POS          => mfb_reconf_tx_eof_pos,
        TX_SOF              => mfb_reconf_tx_sof    ,
        TX_EOF              => mfb_reconf_tx_eof    ,
        TX_SRC_RDY          => mfb_reconf_tx_src_rdy,
        TX_DST_RDY          => mfb_reconf_tx_dst_rdy
    );

    mfb_reconf_tx_dst_rdy <= '0' when ((mfb_reconf_tx_eof(0) = '1') and (mfb_reconf_tx_src_rdy = '1')) and (new_eof(0) = '0') else dst_rdy;

    -- Asserts in the first clock cycle when a valid mfb_reconf_tx_eof first appears on the Reconfigurator's output.
    mfb_reconf_tx_eof_appeared <= mfb_reconf_tx_eof(0) and mfb_reconf_tx_src_rdy and not new_eofpos_offset_vld_reg;

    -- ------------------------------------------
    --  Searching for the new EOF (after append)
    -- ------------------------------------------
    mfb_reconf_tx_eof_pos_arr <= slv_array_deser(mfb_reconf_tx_eof_pos, MFB_REGIONS);

    offset_reached_g : for r in 0 to MFB_REGIONS-1 generate
        new_eofpos_offset(r) <= resize(unsigned(mfb_reconf_tx_eof_pos_arr(r)), OFFSET_WIDTH) +
                                to_unsigned(    r*REGION_ITEMS               , OFFSET_WIDTH) +
                                to_unsigned(    MVB_ITEM_SIZE                , OFFSET_WIDTH);

        new_eofpos_offset_vld(0) <= (mfb_reconf_tx_eof(0) and mfb_reconf_tx_src_rdy) or new_eofpos_offset_vld_reg;

        offset_reached_i : entity work.OFFSET_REACHED
        generic map(
            MAX_WORDS     => PKT_MAX_WORDS,
            REGIONS       => MFB_REGIONS  ,
            REGION_ITEMS  => REGION_ITEMS ,
            OFFSET_WIDTH  => OFFSET_WIDTH ,
            REGION_NUMBER => r
        )
        port map(
            RX_WORD    => word_cnt             (r+1),
            RX_OFFSET  => new_eofpos_offset    (r  ),
            RX_VALID   => new_eofpos_offset_vld(r  ),

            TX_REACHED => new_eof              (r  )
        );
    end generate;

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (mfb_reconf_tx_src_rdy = '1') and (dst_rdy = '1') then
                new_eofpos_offset_vld_reg <= new_eofpos_offset_vld(0);
            end if;
            if (RESET = '1') or ((new_eof(0) = '1') and (dst_rdy = '1')) then
                new_eofpos_offset_vld_reg <= '0';
            end if;
        end if;
    end process;

    -- Top bits can overflow - Region and Word is identified by new_eof.
    new_eof_pos(0) <= unsigned(mfb_reconf_tx_eof_pos_arr(0)) + to_unsigned(MVB_ITEM_SIZE, EOF_POS_WIDTH);

    -- ---------------------------------------
    --  Counting valid words since masked EOF
    -- ---------------------------------------
    word_cnt_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (mfb_reconf_tx_src_rdy = '1') and (dst_rdy = '1') then
                word_cnt(0) <= word_cnt(MFB_REGIONS) + 1;
            end if;
            if (RESET = '1') then
                word_cnt(0) <= (others => '0');
            end if;
        end if;
    end process;

    -- Current (valid) counts are at word_cnt(MFB_REGIONS downto 1) and
    -- word_cnt(0) carries the value from the previous clock cycle
    word_cnt_g: for r in 0 to MFB_REGIONS-1 generate
        word_cnt(r+1) <= (others => '0') when (mfb_reconf_tx_eof_appeared = '1') else word_cnt(r);
    end generate;

    -- ---------------------------------------------------------------
    --  Making the append_vector - '1's indicate Items to be appended
    -- ---------------------------------------------------------------
    append_start_item_idx <= resize(unsigned(mfb_reconf_tx_eof_pos_arr(0)), EOF_POS_WIDTH+1) + 1; -- MSB = overflow = not valid (in this word)
    append_end_item_idx <= unsigned(new_eof_pos(0));

    -- Here = in the current word
    append_begins_here <= not append_start_item_idx(EOF_POS_WIDTH) when (mfb_reconf_tx_eof_appeared = '1') else
                          not append_begins_here_reg1              when (new_eofpos_offset_vld_reg  = '1') else
                          '0';
    append_ends_here   <= new_eof(0);

    offset_lo <= append_start_item_idx(EOF_POS_WIDTH-1 downto 0) when (append_begins_here = '1') else to_unsigned(0, log2(REGION_ITEMS));
    offset_hi <= append_end_item_idx                             when (append_ends_here   = '1') else (others => '1');
    -- Set valid from append_start_item_idx to append_end_item_idx <=> set valid from mfb_reconf_tx_eof_pos+1 to new_eof_pos.
    offset_vld <= not append_start_item_idx(EOF_POS_WIDTH) when (mfb_reconf_tx_eof_appeared = '1') else
                  new_eofpos_offset_vld_reg;

    ones_insertor_i : entity work.ONES_INSERTOR
    generic map(
        OFFSET_WIDTH => log2(REGION_ITEMS)
    )
    port map(
        OFFSET_LOW  => offset_lo ,
        OFFSET_HIGH => offset_hi ,
        VALID       => offset_vld,
        ONES_VECTOR => append_vec
    );

    -- =======================================================================
    -- Stage 1 register
    -- =======================================================================

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (dst_rdy = '1') then
                mfb_data_reg1           <= mfb_reconf_tx_data;
                mfb_meta_reg1           <= mfb_reconf_tx_meta;
                mfb_sof_pos_reg1        <= mfb_reconf_tx_sof_pos;
                mfb_eof_pos_reg1        <= slv_array_ser(u_arr_to_slv_arr(new_eof_pos));
                mfb_sof_reg1            <= mfb_reconf_tx_sof and not new_eofpos_offset_vld_reg;
                mfb_eof_reg1            <= new_eof;
                mfb_old_eof_reg1        <= mfb_reconf_tx_eof;
                mfb_src_rdy_reg1        <= mfb_reconf_tx_src_rdy;
                append_begins_here_reg1 <= append_begins_here;
                append_ends_here_reg1   <= append_ends_here;
                append_vld_reg1         <= offset_vld; -- Appending in this word
                append_shift_reg1       <= std_logic_vector(append_start_item_idx(EOF_POS_WIDTH-1 downto 0));
                append_vec_reg1         <= append_vec;
            end if;
            if (RESET = '1') then
                mfb_src_rdy_reg1 <= '0';
                append_vld_reg1  <= '0';
            end if;
        end if;
    end process;

    -- =======================================================================
    -- Data insertion
    -- =======================================================================

    bs_rx_data    <= std_logic_vector(resize(unsigned(mvb_fifoxm_dout), WORD_WIDTH));
    -- Do not shift when the the shift vector begins at the first Item of the word.
    bs_rx_sel     <= append_shift_reg1;
    bs_rx_src_rdy <= not mvb_fifoxm_empty(0) when (append_begins_here_reg1 = '1') else append_vld_reg1;

    barrel_shifter_gen_piped_i : entity work.BARREL_SHIFTER_GEN_PIPED
    generic map(
        BLOCKS            => WORD_ITEMS    ,
        BLOCK_WIDTH       => MFB_ITEM_WIDTH,
        BAR_SHIFT_LATENCY => 0             ,
        INPUT_REG         => False         ,
        OUTPUT_REG        => False         ,
        SHIFT_LEFT        => True          ,
        METADATA_WIDTH    => 0
    )
    port map(
        CLK         => CLK            ,
        RESET       => RESET          ,

        RX_DATA     => bs_rx_data     ,
        RX_SEL      => bs_rx_sel      ,
        RX_METADATA => (others => '0'),
        RX_SRC_RDY  => bs_rx_src_rdy  ,
        RX_DST_RDY  => open           ,

        TX_DATA     => bs_tx_data     ,
        TX_METADATA => open           ,
        TX_SRC_RDY  => bs_tx_src_rdy  ,
        TX_DST_RDY  => bs_tx_dst_rdy
    );

    bs_tx_dst_rdy <= append_vld_reg1 and mfb_src_rdy_reg1 and mfb_dst_rdy;

    mfb_data_items_arr    <= slv_array_deser(mfb_data_reg1, WORD_ITEMS);
    append_data_items_arr <= slv_array_deser(bs_tx_data   , WORD_ITEMS);
    append_g : for i in 0 to WORD_ITEMS-1 generate
        mfb_data_appended_arr(i) <= append_data_items_arr(i) when (append_vec_reg1(i) = '1') else
                                    mfb_data_items_arr   (i);
    end generate;

    mfb_src_rdy_appended <= mfb_src_rdy_reg1 and bs_tx_src_rdy when (append_vld_reg1 = '1') else
                            mfb_src_rdy_reg1;

    -- =======================================================================
    -- Output register
    -- =======================================================================

    dst_rdy <= mfb_dst_rdy and bs_tx_src_rdy when (append_vld_reg1 = '1') else
               mfb_dst_rdy;

    tx_reconf_g : if RX_MFB_CONF_EQ_TX generate

        mfb_reconf_out_i : entity work.MFB_RECONFIGURATOR
        generic map(
            RX_REGIONS            => 1                             ,
            RX_REGION_SIZE        => 1                             ,
            RX_BLOCK_SIZE         => MFB_REGION_SIZE*MFB_BLOCK_SIZE,
            RX_ITEM_WIDTH         => MFB_ITEM_WIDTH                ,
            TX_REGIONS            => 1                             ,
            TX_REGION_SIZE        => MFB_REGION_SIZE               ,
            TX_BLOCK_SIZE         => MFB_BLOCK_SIZE                ,
            TX_ITEM_WIDTH         => MFB_ITEM_WIDTH                ,
            META_WIDTH            => MFB_META_WIDTH                ,
            META_MODE             => 0                             ,
            FIFO_SIZE             => 512                           ,
            FRAMES_OVER_TX_BLOCK  => 0                             ,
            FRAMES_OVER_TX_REGION => 0                             ,
            DEVICE                => DEVICE
        )
        port map(
            CLK                 => CLK                                 ,
            RESET               => RESET                               ,

            RX_DATA             => slv_array_ser(mfb_data_appended_arr),
            RX_META             => mfb_meta_reg1                       ,
            RX_SOF_POS          => mfb_sof_pos_reg1                    ,
            RX_EOF_POS          => mfb_eof_pos_reg1                    ,
            RX_SOF              => mfb_sof_reg1                        ,
            RX_EOF              => mfb_eof_reg1                        ,
            RX_SRC_RDY          => mfb_src_rdy_appended                ,
            RX_DST_RDY          => mfb_dst_rdy                         ,

            TX_DATA             => TX_MFB_DATA                         ,
            TX_META             => TX_MFB_META                         ,
            TX_SOF_POS          => TX_MFB_SOF_POS                      ,
            TX_EOF_POS          => TX_MFB_EOF_POS                      ,
            TX_SOF              => TX_MFB_SOF                          ,
            TX_EOF              => TX_MFB_EOF                          ,
            TX_SRC_RDY          => TX_MFB_SRC_RDY                      ,
            TX_DST_RDY          => TX_MFB_DST_RDY
        );

    else generate

        mfb_dst_rdy <= TX_MFB_DST_RDY;

        process(CLK)
        begin
            if rising_edge(CLK) then
                if (TX_MFB_DST_RDY = '1') then
                    TX_MFB_DATA    <= slv_array_ser(mfb_data_appended_arr);
                    TX_MFB_META    <= mfb_meta_reg1;
                    TX_MFB_SOF_POS <= mfb_sof_pos_reg1;
                    TX_MFB_EOF_POS <= mfb_eof_pos_reg1;
                    TX_MFB_SOF     <= mfb_sof_reg1;
                    TX_MFB_EOF     <= mfb_eof_reg1;
                    TX_MFB_SRC_RDY <= mfb_src_rdy_appended;
                end if;
                if (RESET = '1') then
                    TX_MFB_SRC_RDY <= '0';
                end if;
            end if;
        end process;

    end generate;

end architecture;
