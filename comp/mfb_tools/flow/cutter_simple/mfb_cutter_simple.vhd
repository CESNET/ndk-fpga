-- mfb_cutter_simple.vhd: Cut items from SOF, simple implementation with limits
-- Copyright (C) 2018 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- This component cuts the specified number of items from each incoming packet. The data which are
-- not cut out, are shifted to the original SOF position and the EOF is lowered by the number of
-- items which have been cut out.
entity MFB_CUTTER_SIMPLE is
    generic (
        -- =======================================================================
        -- MFB DATA BUS CONFIGURATION:
        --
        -- Frame size restrictions:
        --
        -- * For REGION_SIZE =  1: MIN = (CUTTED_ITEMS+CUT_OFF+1)*ITEM_WIDTH bits
        -- * For REGION_SIZE >= 2: MIN = (REGION_SIZE*BLOCK_SIZE+CUTTED_ITEMS+CUT_OFF)*ITEM_WIDTH bits
        -- =======================================================================
        REGIONS        : natural := 2; -- any positive
        REGION_SIZE    : natural := 8; -- any power of two
        BLOCK_SIZE     : natural := 8; -- any power of two except 1
        ITEM_WIDTH     : natural := 8; -- any positive
        -- Width of MFB Metadata
        META_WIDTH     : natural := 0;
        -- Metadata is valid either with:
        --
        -- * SOF (MODE 0)
        -- * EOF (MODE 1)
        META_ALIGNMENT : natural := 0;

        -- =======================================================================
        -- OTHER CONFIGURATION:
        -- =======================================================================

        -- Count of cutted items from SOF+CUT_OFF. Maximum value is REGION_SIZE*BLOCK_SIZE.
        CUTTED_ITEMS   : natural := 4;
        MAX_CUT_OFFSET : natural := 0 -- any power of two
    );
    port (
        -- =======================================================================
        -- CLOCK AND RESET
        -- =======================================================================

        CLK        : in  std_logic;
        RESET      : in  std_logic;

        -- =======================================================================
        -- INPUT MFB INTERFACE WITH CUT ENABLE FLAGS
        -- =======================================================================

        RX_DATA    : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_META    : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0) := (others => '0');
        RX_SOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_SOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_EOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SRC_RDY : in  std_logic;
        RX_DST_RDY : out std_logic;
        -- Enable of cutting, valid with each SOF.
        RX_CUT     : in  std_logic_vector(REGIONS-1 downto 0);
        -- Cut offset. Maximum value is MAX_CUT_OFFSET.
        RX_CUT_OFF : in  std_logic_vector(REGIONS*max(1,log2(MAX_CUT_OFFSET))-1 downto 0) := (others => '0');

        -- =======================================================================
        -- OUTPUT MFB INTERFACE
        -- =======================================================================

        TX_DATA    : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        -- valid on SOF
        TX_META    : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        TX_SOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX_EOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_EOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_SRC_RDY : out std_logic := '0';
        TX_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MFB_CUTTER_SIMPLE is

    type uns_array_t is array (natural range <>) of unsigned;

    constant DATA_WIDTH         : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant REGION_WIDTH       : natural := REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant WORD_ITEMS         : natural := REGIONS*REGION_SIZE*BLOCK_SIZE;
    constant REGION_ITEMS       : natural := REGION_SIZE*BLOCK_SIZE;
    constant REGION_BLOCKS      : natural := REGION_SIZE;
    constant SOF_POS_WIDTH      : natural := max(1,log2(REGION_SIZE));
    constant EOF_POS_WIDTH      : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));
    constant CUT_OFF_WIDTH      : natural := max(1,log2(MAX_CUT_OFFSET));
    constant CUT_OFF_WORD_WIDTH : natural := log2(((MAX_CUT_OFFSET+WORD_ITEMS-1)/WORD_ITEMS)+1);
    constant LOG2_WORD_ITEMS    : natural := log2(WORD_ITEMS);
    constant LOG2_REGION_ITEMS  : natural := log2(REGION_ITEMS);
    constant LOG2_BLOCK_SIZE    : natural := log2(BLOCK_SIZE);
    constant CUT_POS_WIDTH      : natural := max(CUT_OFF_WIDTH,LOG2_WORD_ITEMS)+1;

    signal s_rx_sof_vld               : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_eof_vld               : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_sof_pos_arr           : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal s_rx_eof_pos_arr           : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_rx_meta_arr              : slv_array_t(REGIONS-1 downto 0)(META_WIDTH-1 downto 0);

    signal s_rx_sof_pos_items_arr     : uns_array_t(REGIONS-1 downto 0)(LOG2_REGION_ITEMS-1 downto 0);
    signal s_sof_items                : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal s_mux_sel                  : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal s_sof_sel                  : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal s_sof_sel_prev             : std_logic_vector(WORD_ITEMS downto 0);
    signal s_cut_sel                  : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal s_cut_sel_prev             : std_logic_vector(WORD_ITEMS downto 0) := (others => '0');

    signal s_cutted_items             : uns_array_t(REGIONS-1 downto 0)(LOG2_REGION_ITEMS downto 0);
    signal s_new_eof_pos_curr_arr_wid : uns_array_t(REGIONS-1 downto 0)(LOG2_REGION_ITEMS downto 0);
    signal s_new_eof_pos_curr_arr     : slv_array_t(REGIONS-1 downto 0)(LOG2_REGION_ITEMS-1 downto 0);
    signal s_new_eof_pos_arr          : slv_array_t(REGIONS-1 downto 0)(LOG2_REGION_ITEMS-1 downto 0);
    signal s_new_meta_arr             : slv_array_t(REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal s_new_eof_curr             : std_logic_vector(REGIONS-1 downto 0);
    signal s_new_eof_prev             : std_logic_vector(REGIONS-1 downto 0);
    signal s_new_eof                  : std_logic_vector(REGIONS-1 downto 0);

    signal s_rx_data_reg              : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal s_rx_meta_reg              : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    signal s_rx_sof_pos_reg           : std_logic_vector(REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal s_rx_sof_reg               : std_logic_vector(REGIONS-1 downto 0);
    signal s_new_eof_pos_reg          : slv_array_t(REGIONS-1 downto 0)(LOG2_REGION_ITEMS-1 downto 0);
    signal s_new_meta_reg             : slv_array_t(REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal s_new_eof_reg              : std_logic_vector(REGIONS-1 downto 0);
    signal s_mux_sel_reg              : std_logic_vector(WORD_ITEMS-1 downto 0);
    signal s_new_eof_reg_fix          : std_logic_vector(REGIONS-1 downto 0);
    signal s_new_eof_pos_reg_fix      : slv_array_t(REGIONS-1 downto 0)(LOG2_REGION_ITEMS-1 downto 0);
    signal s_new_meta_reg_fix         : slv_array_t(REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal s_rx_src_rdy_reg           : std_logic;
    signal s_rx_dst_rdy               : std_logic;
    signal s_dst_rdy                  : std_logic;

    signal s_data_big                 : std_logic_vector((WORD_ITEMS+REGION_ITEMS)*ITEM_WIDTH-1 downto 0);
    signal s_data_big_arr             : slv_array_t(WORD_ITEMS+REGION_ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal s_data_muxed_arr           : slv_array_t(WORD_ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);

    signal s_inc_frame                : std_logic_vector(REGIONS downto 0);
    signal s_valid_region             : std_logic_vector(REGIONS-1 downto 0);
    signal s_valid_word               : std_logic;
    signal s_valid_word_mask          : std_logic;

    signal s_tx_data                  : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal s_tx_meta                  : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    signal s_tx_eof_pos               : std_logic_vector(REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal s_tx_eof                   : std_logic_vector(REGIONS-1 downto 0);
    signal s_tx_sof_pos               : std_logic_vector(REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal s_tx_sof                   : std_logic_vector(REGIONS-1 downto 0);
    signal s_tx_src_rdy               : std_logic;

    signal s_rx_cut_off_arr           : slv_array_t(REGIONS-1 downto 0)(CUT_OFF_WIDTH-1 downto 0);

    signal s_rx_cut_off_pos_arr       : uns_array_t(REGIONS-1 downto 0)(CUT_POS_WIDTH-1 downto 0);
    signal s_rx_cut_off_words_arr     : uns_array_t(REGIONS-1 downto 0)(CUT_OFF_WORD_WIDTH-1 downto 0);
    signal s_rx_cut_off_items_arr     : uns_array_t(REGIONS-1 downto 0)(LOG2_WORD_ITEMS-1 downto 0);
    signal s_rx_cut_off_items_reg     : uns_array_t(REGIONS-1 downto 0)(LOG2_WORD_ITEMS-1 downto 0);
    signal s_rx_cut_word_items_arr    : uns_array_t(REGIONS+1-1 downto 0)(LOG2_WORD_ITEMS-1 downto 0);
    signal s_rx_cut_word              : std_logic_vector(REGIONS+1-1 downto 0);
    signal s_rx_cut_word_vld          : std_logic_vector(REGIONS-1 downto 0);

    signal s_cut_off_word_cnt_arr     : uns_array_t(REGIONS-1 downto 0)(CUT_OFF_WORD_WIDTH-1 downto 0);
    signal s_cut_off_rem_words_arr    : uns_array_t(REGIONS-1 downto 0)(CUT_OFF_WORD_WIDTH-1 downto 0);

    signal s_cut_items                : slv_array_t(REGIONS+1-1 downto 0)(WORD_ITEMS-1 downto 0);
    signal s_cut_items_or             : std_logic_vector(WORD_ITEMS-1 downto 0);

    signal s_from_prev_region         : std_logic_vector(REGIONS downto 0);
    signal s_word_sof_region          : std_logic_vector(log2(REGIONS)-1 downto 0);
    signal s_word_sof_region_reg      : std_logic_vector(log2(REGIONS)-1 downto 0);

begin

    -----------------------------------------------------------------------------
    -- PREPARE MFB INPUTS
    -----------------------------------------------------------------------------

    RX_DST_RDY   <= s_rx_dst_rdy or not RX_SRC_RDY;
    s_rx_sof_vld <= RX_SOF and RX_SRC_RDY;
    s_rx_eof_vld <= RX_EOF and RX_SRC_RDY;

    s_rx_sof_pos_arr <= slv_array_downto_deser(RX_SOF_POS,REGIONS,SOF_POS_WIDTH);
    s_rx_eof_pos_arr <= slv_array_downto_deser(RX_EOF_POS,REGIONS,EOF_POS_WIDTH);
    s_rx_meta_arr    <= slv_array_downto_deser(RX_META,REGIONS,META_WIDTH   );
    s_rx_cut_off_arr <= slv_array_downto_deser(RX_CUT_OFF,REGIONS,CUT_OFF_WIDTH);

    -----------------------------------------------------------------------------
    -- COMPUTE SELECTS FOR MULTIPLEXORS
    -----------------------------------------------------------------------------
    -- offset start word
    s_rx_cut_off_words_arr_g : for r in 0 to REGIONS-1 generate
        s_rx_cut_off_words_arr_nb_g : if REGION_BLOCKS > 1 generate
            s_rx_cut_off_pos_arr(r)   <= resize(unsigned(s_rx_cut_off_arr(r)),CUT_POS_WIDTH) + (unsigned(s_rx_sof_pos_arr(r)) & to_unsigned(0,LOG2_BLOCK_SIZE)) + r*REGION_ITEMS;
        end generate;

        s_rx_cut_off_words_arr_bb_g : if REGION_BLOCKS < 2 generate
            s_rx_cut_off_pos_arr(r)   <= resize(unsigned(s_rx_cut_off_arr(r)),CUT_POS_WIDTH) + r*REGION_ITEMS;
        end generate;

        s_rx_cut_off_words_arr(r) <= s_rx_cut_off_pos_arr(r)(LOG2_WORD_ITEMS + CUT_OFF_WORD_WIDTH -1 downto LOG2_WORD_ITEMS);
        s_rx_cut_off_items_arr(r) <= s_rx_cut_off_pos_arr(r)(LOG2_WORD_ITEMS-1 downto 0);
    end generate;

    -- offset pos
    off_pos_cnt_g : for r in 0 to REGIONS-1 generate
        -- cut pos counter
        off_pos_cnt_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    s_cut_off_word_cnt_arr(r) <= (others => '1');
                elsif (s_rx_sof_vld(r) = '1' and s_rx_dst_rdy = '1') then
                    s_cut_off_word_cnt_arr(r) <= s_rx_cut_off_words_arr(r) - 1;
                elsif (s_rx_dst_rdy = '1' and RX_SRC_RDY = '1') then
                    s_cut_off_word_cnt_arr(r) <= s_cut_off_word_cnt_arr(r) - 1;
                end if;
            end if;
        end process;

        -- cut pos vld logic
        cut_word_vld_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    s_rx_cut_word_vld(r) <= '0';
                elsif (s_rx_sof_vld(r) = '1' and s_rx_dst_rdy = '1') then
                    if ((nor s_rx_cut_off_words_arr(r)) = '1') then -- cut is in SOF
                        s_rx_cut_word_vld(r) <= '0';
                    else
                        s_rx_cut_word_vld(r) <= '1';
                    end if;
                elsif (s_rx_dst_rdy = '1' and RX_SRC_RDY = '1') then
                    if ((nor s_cut_off_word_cnt_arr(r)) = '1') then -- word with cut position
                        s_rx_cut_word_vld(r) <= '0';
                    end if;
                end if;
            end if;
        end process;

        s_cut_off_rem_words_arr(r) <= s_rx_cut_off_words_arr(r) when s_rx_sof_vld(r) = '1' else s_cut_off_word_cnt_arr(r);                                    -- remaining items in word
        s_rx_cut_word(r)           <= nor s_cut_off_rem_words_arr(r) when s_rx_sof_vld(r) = '1' else nor s_cut_off_rem_words_arr(r) and s_rx_cut_word_vld(r); -- word with cut offset
    end generate;

    -- cut word cnt selection based on SOF region for packet for prev word
    s_rx_cut_word_g : if REGIONS = 1 generate
        s_rx_cut_word(REGIONS) <= nor s_cut_off_word_cnt_arr(0) and s_rx_cut_word_vld(0) and s_from_prev_region(REGIONS);
    else generate
        s_rx_cut_word(REGIONS) <= nor s_cut_off_word_cnt_arr(to_integer(unsigned(s_word_sof_region_reg))) and s_rx_cut_word_vld(to_integer(unsigned(s_word_sof_region_reg))) and s_from_prev_region(REGIONS);
    end generate;


    -- offset item pos reg
    s_rx_cut_off_items_reg_g : for r in 0 to REGIONS-1 generate
        s_rx_cut_off_items_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (s_rx_sof_vld(r) = '1' and s_rx_dst_rdy = '1') then
                    s_rx_cut_off_items_reg(r) <= s_rx_cut_off_items_arr(r);
                end if;
            end if;
        end process;

        s_rx_cut_word_items_arr(r) <= s_rx_cut_off_items_arr(r) when s_rx_sof_vld(r) = '1' else s_rx_cut_off_items_reg(r);
    end generate;

    s_rx_cut_word_items_arr_g : if REGIONS = 1 generate
        s_rx_cut_word_items_arr(REGIONS) <= s_rx_cut_off_items_reg(0);
    else generate
        s_rx_cut_word_items_arr(REGIONS) <= s_rx_cut_off_items_reg(to_integer(unsigned(s_word_sof_region_reg)));
    end generate;

    -- convert valid cut offset to one-hot format (last is for cut for paket started in prev word)
    off_pos_onehot_g : for r in 0 to REGIONS+1-1 generate

        sof_pos_item_onehot_i : entity work.BIN2HOT
        generic map (
            DATA_WIDTH => LOG2_WORD_ITEMS
        )
        port map (
            EN     => s_rx_cut_word(r),
            INPUT  => std_logic_vector(s_rx_cut_word_items_arr(r)),
            OUTPUT => s_cut_items(r)
        );
    end generate;

    -- merge all cut offsets
    s_cut_items_or <= or_array(s_cut_items);

    -- packet continues from prev region
    s_from_prev_region_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_from_prev_region(0) <= '0';
            elsif (s_rx_dst_rdy = '1' and RX_SRC_RDY = '1') then
                s_from_prev_region(0) <= s_from_prev_region(REGIONS);
            end if;
        end if;
    end process;

    s_from_prev_region_g : for r in 0 to REGIONS-1 generate
        s_from_prev_region(r+1) <= (RX_SOF(r) and not     RX_EOF(r) and not s_from_prev_region(r)) or
                                   (RX_SOF(r) and         RX_EOF(r) and     s_from_prev_region(r)) or
                                   (not RX_SOF(r) and not RX_EOF(r) and     s_from_prev_region(r));
    end generate;

    -- SOF region decoder (decoder get last SOF)
    s_word_sof_region_i : entity work.DEC1FN2B
    generic map (
        ITEMS  => REGIONS
    )
    port map (
        ENABLE => s_from_prev_region(REGIONS) and or RX_SOF,
        DI     => RX_SOF,
        ADDR   => s_word_sof_region
    );

    s_word_sof_region_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_word_sof_region_reg <= (others => '0');
            elsif (or s_rx_sof_vld = '1') then
                s_word_sof_region_reg <= s_word_sof_region;
            end if;
        end if;
    end process;

    -- convert valid SOF_POS to one-hot format
    sof_pos_onehot_g : for r in 0 to REGIONS-1 generate
        rx_sof_pos_items_arr_g : if REGION_BLOCKS > 1 generate
            s_rx_sof_pos_items_arr(r) <= unsigned(s_rx_sof_pos_arr(r)) & to_unsigned(0,LOG2_BLOCK_SIZE);
        end generate;

        rx_sof_pos_items_arrbb_g : if REGION_BLOCKS < 2 generate
            s_rx_sof_pos_items_arr(r) <= to_unsigned(0,LOG2_REGION_ITEMS);
        end generate;

        sof_pos_item_onehot_i : entity work.BIN2HOT
        generic map (
            DATA_WIDTH => LOG2_REGION_ITEMS
        )
        port map (
            EN     => s_rx_sof_vld(r),
            INPUT  => std_logic_vector(s_rx_sof_pos_items_arr(r)),
            OUTPUT => s_sof_items((r+1)*REGION_ITEMS-1 downto r*REGION_ITEMS)
        );
    end generate;

    -- compute selections of data multiplexors
    mux_sel_g : for r in 0 to REGIONS-1 generate
        mux_sel_g2 : for i in 0 to REGION_ITEMS-1 generate
            -- sof mask
            s_sof_sel(r*REGION_ITEMS+i)        <= RX_CUT(r) when (s_sof_items(r*REGION_ITEMS+i) = '1') else s_sof_sel_prev(r*REGION_ITEMS+i);
            s_sof_sel_prev(r*REGION_ITEMS+i+1) <= s_sof_sel(r*REGION_ITEMS+i);

            -- cut mask
            s_cut_sel(r*REGION_ITEMS+i)        <= '0' when (s_sof_items(r*REGION_ITEMS+i) = '1' and s_cut_items_or(r*REGION_ITEMS+i) = '0') else
                                                  s_sof_sel(r*REGION_ITEMS+i) when (s_cut_items_or(r*REGION_ITEMS+i) = '1') else
                                                  s_cut_sel_prev(r*REGION_ITEMS+i);
            s_cut_sel_prev(r*REGION_ITEMS+i+1) <= '0' when (s_sof_items(r*REGION_ITEMS+i) = '1' and s_cut_items_or(r*REGION_ITEMS+i) = '0') else s_cut_sel(r*REGION_ITEMS+i);
        end generate;
    end generate;
    -- final mux sel
    s_mux_sel <= s_sof_sel and s_cut_sel when MAX_CUT_OFFSET > 0 else s_sof_sel;

    mux_sel_prev_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_rx_dst_rdy = '1') then
                s_sof_sel_prev(0) <= s_sof_sel_prev(WORD_ITEMS);
                s_cut_sel_prev(0) <= s_cut_sel_prev(WORD_ITEMS);
            end if;
        end if;
    end process;

    -----------------------------------------------------------------------------
    -- COMPUTE NEW END OF FRAME POSITIONS
    -----------------------------------------------------------------------------

    new_eof_curr_prev_g : for r in 0 to REGIONS-1 generate
        -- count of cutted items in current frame
        s_cutted_items(r) <= to_unsigned(CUTTED_ITEMS,LOG2_REGION_ITEMS+1) when (s_mux_sel(r*REGION_ITEMS) = '1') else (others => '0');

        -- compute new EOF_POS of current frame
        s_new_eof_pos_curr_arr_wid(r) <= ('0' & unsigned(s_rx_eof_pos_arr(r))) - s_cutted_items(r);
        s_new_eof_pos_curr_arr(r)     <= std_logic_vector(s_new_eof_pos_curr_arr_wid(r)(EOF_POS_WIDTH-1 downto 0));

        -- compute new EOF of current and previous region
        s_new_eof_curr(r) <= RX_EOF(r) and not s_new_eof_pos_curr_arr_wid(r)(EOF_POS_WIDTH);
        s_new_eof_prev(r) <= RX_SRC_RDY and RX_EOF(r) and s_new_eof_pos_curr_arr_wid(r)(EOF_POS_WIDTH);
    end generate;

    -- set new correct EOF and EOF_POS
    new_eof_g : for r in 0 to REGIONS-2 generate
        s_new_eof(r)         <= '1' when (s_new_eof_prev(r+1) = '1') else s_new_eof_curr(r);
        s_new_eof_pos_arr(r) <= s_new_eof_pos_curr_arr(r+1) when (s_new_eof_prev(r+1) = '1') else s_new_eof_pos_curr_arr(r);
        s_new_meta_arr   (r) <= s_rx_meta_arr         (r+1) when (s_new_eof_prev(r+1) = '1') else s_rx_meta_arr         (r);
    end generate;
    s_new_eof(REGIONS-1)         <= s_new_eof_curr(REGIONS-1);
    s_new_eof_pos_arr(REGIONS-1) <= s_new_eof_pos_curr_arr(REGIONS-1);
    s_new_meta_arr   (REGIONS-1) <= s_rx_meta_arr         (REGIONS-1);

    -----------------------------------------------------------------------------
    -- MFB REGISTERS
    -----------------------------------------------------------------------------

    s_rx_dst_rdy <= s_dst_rdy or not s_rx_src_rdy_reg;

    rx_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_rx_dst_rdy = '1') then
                s_rx_data_reg     <= RX_DATA;
                s_rx_meta_reg     <= RX_META;
                s_rx_sof_pos_reg  <= RX_SOF_POS;
                s_rx_sof_reg      <= RX_SOF;

                s_new_eof_pos_reg <= s_new_eof_pos_arr;
                s_new_meta_reg    <= s_new_meta_arr;
                s_new_eof_reg     <= s_new_eof;
                s_mux_sel_reg     <= s_mux_sel;
            end if;
        end if;
    end process;

    -- fix EOF and EOF_POS when new EOF overflow to previous word
    new_eof_reg_fix_g : for r in 0 to REGIONS-2 generate
        s_new_eof_reg_fix(r)     <= s_new_eof_reg(r);
        s_new_eof_pos_reg_fix(r) <= s_new_eof_pos_reg(r);
        s_new_meta_reg_fix   (r) <= s_new_meta_reg   (r);
    end generate;
    s_new_eof_reg_fix(REGIONS-1)     <= '1' when (s_new_eof_prev(0) = '1') else s_new_eof_reg(REGIONS-1);
    s_new_eof_pos_reg_fix(REGIONS-1) <= s_new_eof_pos_curr_arr(0) when (s_new_eof_prev(0) = '1') else s_new_eof_pos_reg(REGIONS-1);
    s_new_meta_reg_fix   (REGIONS-1) <= s_new_meta_arr        (0) when (s_new_eof_prev(0) = '1') else s_new_meta_reg   (REGIONS-1);

    rx_src_rdy_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_rx_src_rdy_reg <= '0';
            elsif (s_rx_dst_rdy = '1') then
                s_rx_src_rdy_reg <= RX_SRC_RDY;
            end if;
        end if;
    end process;

    -----------------------------------------------------------------------------
    -- DATA SHIFT MULTIPLEXOR
    -----------------------------------------------------------------------------

    -- create big data array from all current word and first region from next word
    s_data_big     <= RX_DATA(REGION_WIDTH-1 downto 0) & s_rx_data_reg;
    s_data_big_arr <= slv_array_downto_deser(s_data_big,(WORD_ITEMS+REGION_ITEMS),ITEM_WIDTH);

    -- data multiplexor per items
    items_mux_g : for i in 0 to WORD_ITEMS-1 generate
        s_data_muxed_arr(i) <= s_data_big_arr(i+CUTTED_ITEMS) when (s_mux_sel_reg(i) = '1') else s_data_big_arr(i);
    end generate;

    -- --------------------------------------------------------------------------
    --  FRAME STATE LOGIC
    -- --------------------------------------------------------------------------

    inc_frame_g : for r in 0 to REGIONS-1 generate
        s_inc_frame(r+1) <= (s_rx_sof_reg(r) and not s_new_eof_reg_fix(r) and not s_inc_frame(r)) or
                            (s_rx_sof_reg(r) and s_new_eof_reg_fix(r) and s_inc_frame(r)) or
                            (not s_rx_sof_reg(r) and not s_new_eof_reg_fix(r) and s_inc_frame(r));
    end generate;

    inc_frame_last_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_inc_frame(0) <= '0';
            elsif (s_tx_src_rdy = '1' and TX_DST_RDY = '1') then
                s_inc_frame(0) <= s_inc_frame(REGIONS);
            end if;
        end if;
    end process;

    -- recopute valids of regions and valid of word
    valid_region_g : for r in 0 to REGIONS-1 generate
        s_valid_region(r) <= s_rx_sof_reg(r) or s_new_eof_reg_fix(r) or s_inc_frame(r);
    end generate;
    s_valid_word <= (or s_valid_region) and s_rx_src_rdy_reg;

    -- create word valid mask for stoping data transmit when all data are not ready
    s_valid_word_mask <= (s_rx_src_rdy_reg and RX_SRC_RDY) or not s_inc_frame(REGIONS);

    -- allow data transmit when word valid mask and TX_DST_RDY is high
    s_dst_rdy <= s_valid_word_mask and TX_DST_RDY;

    -----------------------------------------------------------------------------
    -- PREPARE TX SIGNALS
    -----------------------------------------------------------------------------

    s_tx_data    <= slv_array_ser(s_data_muxed_arr,WORD_ITEMS,ITEM_WIDTH);
    s_tx_meta    <= tsel(META_ALIGNMENT = 1, slv_array_ser(s_new_meta_reg_fix), s_rx_meta_reg);
    s_tx_eof_pos <= slv_array_ser(s_new_eof_pos_reg_fix,REGIONS,EOF_POS_WIDTH);
    s_tx_eof     <= s_new_eof_reg_fix;
    s_tx_sof_pos <= s_rx_sof_pos_reg;
    s_tx_sof     <= s_rx_sof_reg;
    s_tx_src_rdy <= s_valid_word and s_valid_word_mask;

    -- --------------------------------------------------------------------------
    --  OUTPUT MFB REGISTER
    -- --------------------------------------------------------------------------

    tx_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1') then
                TX_DATA    <= s_tx_data;
                TX_META    <= s_tx_meta;
                TX_SOF_POS <= s_tx_sof_pos;
                TX_EOF_POS <= s_tx_eof_pos;
                TX_SOF     <= s_tx_sof;
                TX_EOF     <= s_tx_eof;
            end if;
        end if;
    end process;

    tx_src_rdy_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                TX_SRC_RDY <= '0';
            elsif (TX_DST_RDY = '1') then
                TX_SRC_RDY <= s_tx_src_rdy;
            end if;
        end if;
    end process;

end architecture;
