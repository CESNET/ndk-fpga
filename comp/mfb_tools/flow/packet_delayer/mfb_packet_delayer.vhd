-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- =========================================================================
--  Description
-- =========================================================================

-- Incoming packets with Timestamps [ns] are stored in the RX FIFO.
-- From there each packet is read when the Stored time value reaches the packet's Timestamp value.
-- There are 2 Timestamp formats that are currently supported (see the :vhdl:genconstant:`TS_FORMAT <mfb_packet_delayer.ts_format>` generic).
-- The packets read from the RX FIFO are stored in the TX FIFO.
--
entity MFB_PACKET_DELAYER is
generic(
    -- Number of Regions within a data word, must be power of 2.
    MFB_REGIONS           : natural := 1;
    -- Region size (in Blocks).
    MFB_REGION_SIZE       : natural := 8;
    -- Block size (in Items), must be 8.
    MFB_BLOCK_SIZE        : natural := 8;
    -- Item width (in bits), must be 8.
    MFB_ITEM_WIDTH        : natural := 8;
    -- Metadata width (in bits).
    MFB_META_WIDTH        : natural := 0;

    -- Width of Timestamps (in bits).
    TS_WIDTH              : natural := 48;
    -- Format of Timestamps. Options:
    --
    -- - ``0`` number of NS between individual packets,
    -- - ``1`` number of NS from RESET.
    TS_FORMAT             : natural := 0;
    -- Number of Items in the Input MFB_FIFOX (main buffer).
    FIFO_DEPTH            : natural := 2048;
    -- Almost Full Offset of the Input MFB_FIFOX.
    -- Pauses the appropriate DMA channel when the amount of stored Items reaches this value.
    FIFO_AF_OFFSET        : natural := 1000;
    -- Almost Empty Offset of the input MFB_FIFOX.
    -- Unpauses (resumes) the appropriate DMA channel when the amount of stored Items drops under this value.
    FIFO_AE_OFFSET        : natural := 1000;

    -- FPGA device name: ULTRASCALE, STRATIX10, AGILEX, ...
    DEVICE                : string := "STRATIX10"
);
port(
    -- =====================================================================
    --  Clock and Reset
    -- =====================================================================

    CLK            : in  std_logic;
    RESET          : in  std_logic;

    -- Reset time accumulation (applies only when TS_FORMAT=1).
    -- Time counter is reset with the next first SOF.
    TIME_RESET     : in  std_logic;

    -- A 64-bit value representing Time, which is used to decide whether a packet's Timestamp is OK and can be transmitted or not.
    -- It can be a precise time from the TSU, a value from a simple incrementing counter, or anything in between.
    -- The quality of the time source affects the precision of the packet's transmission but not the component's functionality.
    CURRENT_TIME   : in  std_logic_vector(64-1 downto 0);

    -- Used to pause incomming traffic when the buffer is Almost Full.
    PAUSE_REQUEST  : out std_logic;

    -- =====================================================================
    --  RX inf
    -- =====================================================================

    RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- Valid with SOF.
    RX_MFB_META    : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
    -- Timestamp valid with each SOF.
    RX_MFB_TS      : in  std_logic_vector(MFB_REGIONS*TS_WIDTH-1 downto 0) := (others => '0');
    RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_SRC_RDY : in  std_logic;
    RX_MFB_DST_RDY : out std_logic;

    -- =====================================================================
    --  TX inf
    -- =====================================================================

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

architecture FULL of MFB_PACKET_DELAYER is

    subtype my_integer is integer range MFB_REGION_SIZE-1 downto 0;
    type my_integer_vector is array(natural range <>) of my_integer;

    -- ========================================================================
    --                                CONSTANTS
    -- ========================================================================

    constant WORD_WIDTH    : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant REGION_WIDTH  : natural := WORD_WIDTH/MFB_REGIONS;
    constant WORD_BLOCKS   : natural := MFB_REGIONS*MFB_REGION_SIZE;
    constant BLOCK_WIDTH   : natural := WORD_WIDTH/WORD_BLOCKS;
    constant SOF_POS_WIDTH : natural := max(1,log2(MFB_REGION_SIZE));
    constant EOF_POS_WIDTH : natural := max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));

    --                                      Meta           + Timestamps
    constant RX_META_WIDTH_EXT : natural := MFB_META_WIDTH + TS_WIDTH;

    -- ========================================================================
    --                                 SIGNALS
    -- ========================================================================

    signal rx_fifo_afull                : std_logic;
    signal rx_fifo_aempty               : std_logic;

    signal rx_mfb_meta_regions_arr      : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH   -1 downto 0);
    signal rx_mfb_ts_regions_arr        : slv_array_t     (MFB_REGIONS-1 downto 0)(TS_WIDTH         -1 downto 0);
    signal rx_mfb_meta_plus_arr         : slv_array_t     (MFB_REGIONS-1 downto 0)(RX_META_WIDTH_EXT-1 downto 0);
    signal rx_mfb_meta_plus             : std_logic_vector(MFB_REGIONS*            RX_META_WIDTH_EXT-1 downto 0);

    signal fm_rx_data                   : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal fm_rx_meta_plus              : std_logic_vector(MFB_REGIONS*RX_META_WIDTH_EXT-1 downto 0);
    signal fm_rx_sof_pos                : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal fm_rx_eof_pos                : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal fm_rx_sof                    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fm_rx_eof                    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fm_rx_src_rdy                : std_logic;
    signal fm_rx_dst_rdy                : std_logic;

    signal fm_tx_data                   : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal fm_tx_meta_plus              : std_logic_vector(MFB_REGIONS*RX_META_WIDTH_EXT-1 downto 0);
    signal fm_tx_sof_pos                : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal fm_tx_eof_pos                : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal fm_tx_sof                    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fm_tx_eof                    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fm_tx_src_rdy                : std_logic;
    signal fm_tx_dst_rdy                : std_logic;

    signal fm_tx_sof_unmasked           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fm_tx_src_rdy_unmasked       : std_logic;
    signal fm_tx_mask                   : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal fm_tx_meta_plus_arr          : slv_array_t     (MFB_REGIONS-1 downto 0)(RX_META_WIDTH_EXT-1 downto 0);
    signal fm_tx_meta                   : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH   -1 downto 0);
    signal fm_tx_ts                     : slv_array_t     (MFB_REGIONS-1 downto 0)(TS_WIDTH         -1 downto 0);

    signal ts_ok                        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fm_tx_sof_to_read            : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal sof_read                     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal first_sof_read               : std_logic;
    signal waiting_for_first_sof        : std_logic;
    signal update_stored_time           : std_logic;
    signal current_time_reg             : unsigned(64-1 downto 0);
    signal one_clk_period_time_diff     : unsigned                         (TS_WIDTH-1 downto 0);
    signal stored_time_diff             : unsigned                         (TS_WIDTH-1 downto 0);
    signal stored_time_diff_fixed       : u_array_t(MFB_REGIONS-1 downto 0)(TS_WIDTH-1 downto 0);

    signal mfb_data_mid_reg             : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal mfb_meta_mid_reg             : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal mfb_sof_pos_mid_reg          : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal mfb_eof_pos_mid_reg          : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal mfb_sof_mid_reg              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_eof_mid_reg              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_src_rdy_mid_reg          : std_logic;
    signal mfb_dst_rdy_mid_reg          : std_logic;

begin

    -- Pause incomming traffic when RX FIFO is getting full.
    -- Restart it again after some of its contents have been read.
    process(CLK)
    begin
        if rising_edge(CLK) then
            if (rx_fifo_afull = '1') then
                PAUSE_REQUEST <= '1';
            end if;
            if (RESET = '1') or (rx_fifo_aempty = '1') then
                PAUSE_REQUEST <= '0';
            end if;
        end if;
    end process;

    rx_mfb_meta_regions_arr <= slv_array_deser(RX_MFB_META, MFB_REGIONS);
    rx_mfb_ts_regions_arr   <= slv_array_deser(RX_MFB_TS  , MFB_REGIONS);
    rx_fifo_meta_g : for r in 0 to MFB_REGIONS-1 generate
        rx_mfb_meta_plus_arr(r) <= rx_mfb_meta_regions_arr(r) & rx_mfb_ts_regions_arr(r);
    end generate;
    rx_mfb_meta_plus <= slv_array_ser(rx_mfb_meta_plus_arr);

    -- ========================================================================
    -- RX FIFO
    -- ========================================================================

    rx_mfb_fifox_i : entity work.MFB_FIFOX
    generic map(
        REGIONS             => MFB_REGIONS      ,
        REGION_SIZE         => MFB_REGION_SIZE  ,
        BLOCK_SIZE          => MFB_BLOCK_SIZE   ,
        ITEM_WIDTH          => MFB_ITEM_WIDTH   ,
        META_WIDTH          => RX_META_WIDTH_EXT,
        FIFO_DEPTH          => FIFO_DEPTH       ,
        RAM_TYPE            => "AUTO"           ,
        DEVICE              => DEVICE           ,
        ALMOST_FULL_OFFSET  => FIFO_AF_OFFSET   ,
        ALMOST_EMPTY_OFFSET => FIFO_AE_OFFSET
    )
    port map(
        CLK => CLK,
        RST => RESET,

        RX_DATA     => RX_MFB_DATA     ,
        RX_META     => rx_mfb_meta_plus,
        RX_SOF_POS  => RX_MFB_SOF_POS  ,
        RX_EOF_POS  => RX_MFB_EOF_POS  ,
        RX_SOF      => RX_MFB_SOF      ,
        RX_EOF      => RX_MFB_EOF      ,
        RX_SRC_RDY  => RX_MFB_SRC_RDY  ,
        RX_DST_RDY  => RX_MFB_DST_RDY  ,

        TX_DATA     => fm_rx_data      ,
        TX_META     => fm_rx_meta_plus ,
        TX_SOF_POS  => fm_rx_sof_pos   ,
        TX_EOF_POS  => fm_rx_eof_pos   ,
        TX_SOF      => fm_rx_sof       ,
        TX_EOF      => fm_rx_eof       ,
        TX_SRC_RDY  => fm_rx_src_rdy   ,
        TX_DST_RDY  => fm_rx_dst_rdy   ,

        FIFO_STATUS => open            ,
        FIFO_AFULL  => rx_fifo_afull   ,
        FIFO_AEMPTY => rx_fifo_aempty
    );

    frame_masker_i : entity work.MFB_FRAME_MASKER
    generic map(
        REGIONS     => MFB_REGIONS      ,
        REGION_SIZE => MFB_REGION_SIZE  ,
        BLOCK_SIZE  => MFB_BLOCK_SIZE   ,
        ITEM_WIDTH  => MFB_ITEM_WIDTH   ,
        META_WIDTH  => RX_META_WIDTH_EXT,
        USE_PIPE    => False            ,
        PIPE_TYPE   => "SHREG"          ,
        DEVICE      => DEVICE
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        RX_DATA             => fm_rx_data            ,
        RX_META             => fm_rx_meta_plus       ,
        RX_SOF_POS          => fm_rx_sof_pos         ,
        RX_EOF_POS          => fm_rx_eof_pos         ,
        RX_SOF              => fm_rx_sof             ,
        RX_EOF              => fm_rx_eof             ,
        RX_SRC_RDY          => fm_rx_src_rdy         ,
        RX_DST_RDY          => fm_rx_dst_rdy         ,

        TX_DATA             => fm_tx_data            ,
        TX_META             => fm_tx_meta_plus       ,
        TX_SOF_POS          => fm_tx_sof_pos         ,
        TX_EOF_POS          => fm_tx_eof_pos         ,
        TX_SOF_MASKED       => fm_tx_sof             , -- open - can prepare my own
        TX_EOF_MASKED       => fm_tx_eof             ,
        TX_SRC_RDY          => fm_tx_src_rdy         ,
        TX_DST_RDY          => fm_tx_dst_rdy         ,

        TX_SOF_UNMASKED     => fm_tx_sof_unmasked    ,
        TX_EOF_UNMASKED     => open                  ,
        TX_SRC_RDY_UNMASKED => fm_tx_src_rdy_unmasked,

        TX_SOF_ORIGINAL     => open                  ,
        TX_EOF_ORIGINAL     => open                  ,
        TX_SRC_RDY_ORIGINAL => open                  ,

        TX_MASK             => fm_tx_mask
    );

    fm_tx_meta_plus_arr <= slv_array_deser(fm_tx_meta_plus, MFB_REGIONS);
    fifoxm_out_meta_g : for r in 0 to MFB_REGIONS-1 generate
        fm_tx_meta(r) <= fm_tx_meta_plus_arr(r)(RX_META_WIDTH_EXT-1 downto TS_WIDTH);
        fm_tx_ts  (r) <= fm_tx_meta_plus_arr(r)(TS_WIDTH         -1 downto 0);
    end generate;

    ts_ok_g : for r in 0 to MFB_REGIONS-1 generate
        ts_ok(r) <= '1' when (stored_time_diff_fixed(r) >= unsigned(fm_tx_ts(r))) else '0';
    end generate;
    fm_tx_sof_to_read <= (fm_tx_sof_unmasked and fm_tx_src_rdy_unmasked) and ts_ok;
    fm_tx_mask <= fm_tx_sof_to_read;

    fm_tx_dst_rdy <= mfb_dst_rdy_mid_reg;

    -- ========================================================================
    -- Time logic
    -- ========================================================================

    sof_read <= fm_tx_sof;

    reset_g : if TS_FORMAT=0 generate
        -- Store new value of CURRENT_TIME with each read SOF
        update_stored_time <= or sof_read;
    else generate
        -- Store new value of CURRENT_TIME when the first SOF is read
        update_stored_time <= first_sof_read;

        first_sof_read <= (or sof_read) and waiting_for_first_sof;
        process(CLK)
        begin
            if rising_edge(CLK) then
                if (RESET = '1') or (TIME_RESET = '1') then
                    waiting_for_first_sof <= '1';
                end if;
                if ((or sof_read) = '1') then
                    waiting_for_first_sof <= '0';
                end if;
            end if;
        end process;
    end generate;

    -- Get the duration of a single clock period in [ns]
    process(CLK)
    begin
        if rising_edge(CLK) then
            current_time_reg <= unsigned(CURRENT_TIME);
        end if;
    end process;
    one_clk_period_time_diff <= resize(unsigned(CURRENT_TIME)-current_time_reg, TS_WIDTH);

    -- Update the time difference that is then used for comparison with the packet's Timestamp
    process(CLK)
    begin
        if rising_edge(CLK) then
            -- Accumulate time until update_stored_time='1'
            stored_time_diff <= resize(stored_time_diff+one_clk_period_time_diff, TS_WIDTH);
            if (update_stored_time = '1') then
                -- Basically a reset, but to the duration of one clock period instead of 0 [ns]
                stored_time_diff <= one_clk_period_time_diff;
            end if;
            if (RESET = '1') then
                stored_time_diff <= (others => '0');
            end if;
        end if;
    end process;

    stored_time_diff_fixed(0) <= stored_time_diff;
    -- when on of the previous Regions with SOF were read, "fix" the time in the current word (set it to 0 ns)
    fix_time_g : for r in 0 to MFB_REGIONS-2 generate
        stored_time_diff_fixed(r+1) <= stored_time_diff when (or sof_read(r downto 0) = '0') else (others => '0');
    end generate;

    -- Another version for the stored_time_diff_fixed signal above
    -- process(all)
    -- begin
    --     stored_time_diff_fixed <= (others => stored_time_diff);
    --     for r in 0 to MFB_REGIONS-1 loop
    --         if (sof_read(r) = '1') then
    --             stored_time_diff_fixed(r to MFB_REGIONS-1) <= (others => '0');
    --             exit; -- this might be unnecessary
    --         end if;
    --     end loop;
    -- end process;

    -- ========================================================================
    -- Middle register
    -- ========================================================================

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (mfb_dst_rdy_mid_reg = '1') then
                mfb_data_mid_reg    <= fm_tx_data;
                mfb_meta_mid_reg    <= slv_array_ser(fm_tx_meta);
                mfb_sof_pos_mid_reg <= fm_tx_sof_pos;
                mfb_eof_pos_mid_reg <= fm_tx_eof_pos;
                mfb_sof_mid_reg     <= fm_tx_sof;
                mfb_eof_mid_reg     <= fm_tx_eof;
                mfb_src_rdy_mid_reg <= fm_tx_src_rdy and fm_tx_dst_rdy; -- (and fm_tx_dst_rdy) might be unnecessary
            end if;
            if (RESET = '1') then
                mfb_src_rdy_mid_reg <= '0';
            end if;
        end if;
    end process;

    -- ========================================================================
    -- TX MFB FIFOX
    -- ========================================================================

    tx_mfb_fifox_i : entity work.MFB_FIFOX
    generic map(
        REGIONS             => MFB_REGIONS    ,
        REGION_SIZE         => MFB_REGION_SIZE,
        BLOCK_SIZE          => MFB_BLOCK_SIZE ,
        ITEM_WIDTH          => MFB_ITEM_WIDTH ,
        META_WIDTH          => MFB_META_WIDTH ,
        FIFO_DEPTH          => 512            ,
        RAM_TYPE            => "AUTO"         ,
        DEVICE              => DEVICE         ,
        ALMOST_FULL_OFFSET  => 0              ,
        ALMOST_EMPTY_OFFSET => 0
    )
    port map(
        CLK => CLK,
        RST => RESET,

        RX_DATA     => mfb_data_mid_reg   ,
        RX_META     => mfb_meta_mid_reg   ,
        RX_SOF_POS  => mfb_sof_pos_mid_reg,
        RX_EOF_POS  => mfb_eof_pos_mid_reg,
        RX_SOF      => mfb_sof_mid_reg    ,
        RX_EOF      => mfb_eof_mid_reg    ,
        RX_SRC_RDY  => mfb_src_rdy_mid_reg,
        RX_DST_RDY  => mfb_dst_rdy_mid_reg,

        TX_DATA     => TX_MFB_DATA        ,
        TX_META     => TX_MFB_META        ,
        TX_SOF_POS  => TX_MFB_SOF_POS     ,
        TX_EOF_POS  => TX_MFB_EOF_POS     ,
        TX_SOF      => TX_MFB_SOF         ,
        TX_EOF      => TX_MFB_EOF         ,
        TX_SRC_RDY  => TX_MFB_SRC_RDY     ,
        TX_DST_RDY  => TX_MFB_DST_RDY     ,

        FIFO_STATUS => open               ,
        FIFO_AFULL  => open               ,
        FIFO_AEMPTY => open
    );

end architecture;
