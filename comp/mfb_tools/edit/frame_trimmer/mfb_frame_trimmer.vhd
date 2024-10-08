-- mfb_frame_trimmer.vhd:
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The MFB_FRAME_TRIMMER component allows shortening of MFB frames to a selected
-- length. The current implementation is minimalist and does not allow any data
-- shifts. Therefore, there are few restrictions for the new frame length:
-- - max value is original frame length
-- - min value is ((BLOCK_SIZE*ITEM_WIDTH)-(ITEM_WIDTH-1))
entity MFB_FRAME_TRIMMER is
    generic(
        REGIONS     : natural := 4;
        REGION_SIZE : natural := 8;
        BLOCK_SIZE  : natural := 8;
        ITEM_WIDTH  : natural := 8;
        META_WIDTH  : natural := 8;
        LEN_WIDTH   : natural := 14;
        DEVICE      : string  := "AGILEX"
    );
    port(
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- Enable frame trimming, valid with RX_SOF.
        RX_TRIM_EN     : in  std_logic_vector(REGIONS-1 downto 0);
        -- New frame length after trimming in ITEMS, max value is original frame
        -- length, min value is ((BLOCK_SIZE*ITEM_WIDTH)-(ITEM_WIDTH-1)).
        -- The new length is valid with RX_TRIM_EN.
        RX_TRIM_LEN    : in  std_logic_vector(REGIONS*LEN_WIDTH-1 downto 0);
        RX_DATA        : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        -- User metadata valid with RX_SOF.
        RX_META        : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        RX_SOF_POS     : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_EOF_POS     : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SOF         : in  std_logic_vector(REGIONS-1 downto 0);
        RX_EOF         : in  std_logic_vector(REGIONS-1 downto 0);
        RX_SRC_RDY     : in  std_logic;
        RX_DST_RDY     : out std_logic;

        TX_DATA        : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        -- User metadata valid with TX_SOF.
        TX_META        : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        TX_SOF_POS     : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_EOF_POS     : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_SOF         : out std_logic_vector(REGIONS-1 downto 0);
        TX_EOF         : out std_logic_vector(REGIONS-1 downto 0);
        TX_SRC_RDY     : out std_logic;
        TX_DST_RDY     : in  std_logic
    );
end entity;

architecture FULL of MFB_FRAME_TRIMMER is

    constant REGION_ITEMS   : natural := REGION_SIZE*BLOCK_SIZE;
    constant SOF_POS_WIDTH  : natural := log2(REGION_SIZE);
    constant EOF_POS_WIDTH  : natural := log2(REGION_ITEMS);
    constant WORD_BLOCKS    : natural := REGIONS*REGION_SIZE;
    constant WORD_ITEMS     : natural := REGIONS*REGION_ITEMS;
    constant WORD_CNT_WIDTH : natural := LEN_WIDTH - log2(WORD_ITEMS);

    signal s_rx_word_cnt             : u_array_t(REGIONS-1 downto 0)(WORD_CNT_WIDTH-1 downto 0);
    signal s_rx_word_cnt_prev        : u_array_t(REGIONS-1 downto 0)(WORD_CNT_WIDTH-1 downto 0);
    signal s_rx_word_cnt_reg         : unsigned(WORD_CNT_WIDTH-1 downto 0);

    signal s_rx_sof_pos              : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal s_rx_eof_pos              : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_rx_new_len              : slv_array_t(REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);

    signal s_rx_sof_pos_ext          : u_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_rx_eof_pos_blk          : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal s_rx_sof_after_eof        : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_sof_after_eof_vld    : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_sof_before_eof_vld   : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_new_len_ext_curr     : u_array_t(REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal s_rx_new_len_ext          : u_array_t(REGIONS+1-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal s_trim_lvld               : std_logic_vector(REGIONS+1-1 downto 0);
    signal s_trim_fpir               : std_logic_vector(REGIONS-1 downto 0);
    signal s_nl_word_off             : u_array_t(REGIONS-1 downto 0)(WORD_CNT_WIDTH-1 downto 0);
    signal s_nl_region_off           : u_array_t(REGIONS-1 downto 0)(log2(REGIONS)-1 downto 0);
    signal s_nl_block_off            : u_array_t(REGIONS-1 downto 0)(log2(REGION_SIZE)-1 downto 0);
    signal s_nl_pos_off              : u_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_nl_word_off_prev        : u_array_t(REGIONS-1 downto 0)(WORD_CNT_WIDTH-1 downto 0);
    signal s_nl_region_off_prev      : u_array_t(REGIONS-1 downto 0)(log2(REGIONS)-1 downto 0);
    signal s_nl_block_off_prev       : u_array_t(REGIONS-1 downto 0)(log2(REGION_SIZE)-1 downto 0);
    signal s_nl_pos_off_prev         : u_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_nl_word_ok              : std_logic_vector(REGIONS-1 downto 0);
    signal s_nl_region_ok            : std_logic_vector(REGIONS-1 downto 0);
    signal s_nl_word_prev_ok         : std_logic_vector(REGIONS-1 downto 0);
    signal s_nl_region_prev_ok       : std_logic_vector(REGIONS-1 downto 0);
    signal s_nl_ok                   : std_logic_vector(REGIONS-1 downto 0);
    signal s_nl_prev_ok              : std_logic_vector(REGIONS-1 downto 0);

    signal s_rx_eof_masked           : std_logic_vector(REGIONS-1 downto 0);
    signal s_new_eof                 : std_logic_vector(REGIONS-1 downto 0);
    signal s_new_eof_pos             : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_final_eof               : std_logic_vector(REGIONS-1 downto 0);
    signal s_final_eof_pos           : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);

    signal s_inc_pkt                 : std_logic_vector(REGIONS+1-1 downto 0);
    signal s_region_vld              : std_logic_vector(REGIONS-1 downto 0);
    signal s_src_rdy                 : std_logic;

    signal s_data_reg0               : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal s_meta_reg0               : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    signal s_sof_pos_reg0            : std_logic_vector(REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal s_eof_pos_reg0            : std_logic_vector(REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal s_sof_reg0                : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_reg0                : std_logic_vector(REGIONS-1 downto 0);
    signal s_src_rdy_reg0            : std_logic;

begin

    RX_DST_RDY <= TX_DST_RDY;

    -- =========================================================================
    --  0. LOGIC STAGE
    -- =========================================================================

    -- -------------------------------------------------------------------------
    -- WORD COUNTER
    -- -------------------------------------------------------------------------

    rx_word_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_rx_word_cnt_reg <= (others => '0');
            elsif (TX_DST_RDY = '1' and RX_SRC_RDY = '1') then
                s_rx_word_cnt_reg <= s_rx_word_cnt(REGIONS-1) + 1;
            end if;
        end if;
    end process;

    s_rx_word_cnt(0) <= (others => '0') when ((RX_SOF(0) = '1')) else s_rx_word_cnt_reg;
    rx_word_cnt_g : for r in 1 to REGIONS-1 generate
        s_rx_word_cnt(r) <= (others => '0') when (RX_SOF(r) = '1') else s_rx_word_cnt(r-1);
    end generate;

    s_rx_word_cnt_prev(0) <= s_rx_word_cnt_reg;
    rx_word_cnt_prev_g : for r in 1 to REGIONS-1 generate
        s_rx_word_cnt_prev(r) <= (others => '0') when (RX_SOF(r-1) = '1') else s_rx_word_cnt(r-1);
    end generate;

    -- -------------------------------------------------------------------------
    -- PACKET PREPARE
    -- -------------------------------------------------------------------------

    s_rx_sof_pos <= slv_array_deser(RX_SOF_POS, REGIONS);
    s_rx_eof_pos <= slv_array_deser(RX_EOF_POS, REGIONS);
    s_rx_new_len <= slv_array_deser(RX_TRIM_LEN, REGIONS);

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1' and RX_SRC_RDY = '1') then
                s_rx_new_len_ext(0) <= s_rx_new_len_ext(REGIONS);
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_trim_lvld(0) <= '0';
            elsif (TX_DST_RDY = '1' and RX_SRC_RDY = '1') then
                s_trim_lvld(0) <= s_trim_lvld(REGIONS);
            end if;
        end if;
    end process;

    new_len_g : for r in 0 to REGIONS-1 generate
        s_rx_sof_pos_ext(r) <= unsigned(s_rx_sof_pos(r)) & to_unsigned(0,log2(BLOCK_SIZE));
        s_rx_eof_pos_blk(r) <= s_rx_eof_pos(r)(EOF_POS_WIDTH-1 downto log2(BLOCK_SIZE));

        s_rx_sof_after_eof(r)      <= '1' when (unsigned(s_rx_sof_pos(r)) > unsigned(s_rx_eof_pos_blk(r))) else '0';
        s_rx_sof_after_eof_vld(r)  <= s_rx_sof_after_eof(r) and RX_SOF(r) and RX_EOF(r);
        s_rx_sof_before_eof_vld(r) <= not s_rx_sof_after_eof(r) and RX_SOF(r) and RX_EOF(r);

        s_rx_new_len_ext_curr(r) <= unsigned(s_rx_new_len(r)) + (r*REGION_SIZE*BLOCK_SIZE) + s_rx_sof_pos_ext(r) - 1;
        s_rx_new_len_ext(r+1)    <= s_rx_new_len_ext_curr(r) when (RX_SOF(r) = '1') else s_rx_new_len_ext(r);

        -- last valid of trim valid
        s_trim_lvld(r+1) <= RX_TRIM_EN(r) when (RX_SOF(r) = '1') else s_trim_lvld(r);
        -- trim valid of first packet in region
        s_trim_fpir(r) <= RX_TRIM_EN(r) when (s_rx_sof_before_eof_vld(r) = '1') else s_trim_lvld(r);

        s_nl_word_off(r)        <= s_rx_new_len_ext(r+1)(LEN_WIDTH-1 downto log2(REGIONS*REGION_ITEMS));
        s_nl_region_off(r)      <= s_rx_new_len_ext(r+1)(log2(REGIONS*REGION_ITEMS)-1 downto log2(REGION_ITEMS));
        s_nl_block_off(r)       <= s_rx_new_len_ext(r+1)(log2(REGION_ITEMS)-1 downto log2(BLOCK_SIZE));
        s_nl_pos_off(r)         <= s_rx_new_len_ext(r+1)(log2(REGION_ITEMS)-1 downto 0);
        s_nl_word_off_prev(r)   <= s_rx_new_len_ext(r)(LEN_WIDTH-1 downto log2(REGIONS*REGION_ITEMS));
        s_nl_region_off_prev(r) <= s_rx_new_len_ext(r)(log2(REGIONS*REGION_ITEMS)-1 downto log2(REGION_ITEMS));
        s_nl_block_off_prev(r)  <= s_rx_new_len_ext(r)(log2(REGION_ITEMS)-1 downto log2(BLOCK_SIZE));
        s_nl_pos_off_prev(r)    <= s_rx_new_len_ext(r)(log2(REGION_ITEMS)-1 downto 0);

        s_nl_word_ok(r)        <= '1' when ((s_nl_word_off(r) = s_rx_word_cnt(r)))           else '0';
        s_nl_region_ok(r)      <= '1' when ((REGIONS = 1) or (s_nl_region_off(r) = r))       else '0';
        s_nl_word_prev_ok(r)   <= '1' when ((s_nl_word_off_prev(r) = s_rx_word_cnt_prev(r))) else '0';
        s_nl_region_prev_ok(r) <= '1' when ((REGIONS = 1) or (s_nl_region_off_prev(r) = r))  else '0';

        s_nl_ok(r)      <= s_nl_word_ok(r) and s_nl_region_ok(r) and s_trim_lvld(r+1);
        s_nl_prev_ok(r) <= s_nl_word_prev_ok(r) and s_nl_region_prev_ok(r) and s_trim_lvld(r) and s_rx_sof_after_eof_vld(r);
    end generate;

    -- --------------------------------------------------------------------------
    -- FINAL EOF and EOF_POS
    -- --------------------------------------------------------------------------

    final_eof_g : for r in 0 to REGIONS-1 generate
        -- New EOF for trimmed frames
        s_new_eof(r)     <= s_nl_ok(r) or s_nl_prev_ok(r);
        s_new_eof_pos(r) <= std_logic_vector(s_nl_pos_off(r)) when (s_nl_ok(r) = '1') else std_logic_vector(s_nl_pos_off_prev(r));
        -- EOF for NON-trimmed frames
        s_rx_eof_masked(r) <= RX_EOF(r) and not s_trim_fpir(r);
        -- Final EOF logic
        s_final_eof(r)     <= s_new_eof(r) or s_rx_eof_masked(r);
        s_final_eof_pos(r) <= s_new_eof_pos(r) when (s_new_eof(r) = '1') else s_rx_eof_pos(r);
    end generate;

    ----------------------------------------------------------------------------
    -- SRC_RDY RECALCULATE
    ----------------------------------------------------------------------------

    inc_pkt_g : for r in 0 to REGIONS-1 generate
        s_inc_pkt(r+1) <= (RX_SOF(r) and not s_final_eof(r) and not s_inc_pkt(r)) or
                          (RX_SOF(r) and s_final_eof(r) and s_inc_pkt(r)) or
                          (not RX_SOF(r) and not s_final_eof(r) and s_inc_pkt(r));
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_inc_pkt(0) <= '0';
            elsif (RX_SRC_RDY = '1' and TX_DST_RDY = '1') then
                s_inc_pkt(0) <= s_inc_pkt(REGIONS);
            end if;
        end if;
    end process;

    -- calculate valid of regions
    region_vld_g : for r in 0 to REGIONS-1 generate
        s_region_vld(r) <= RX_SOF(r) or s_inc_pkt(r);
    end generate;

    s_src_rdy <= (or s_region_vld) and RX_SRC_RDY;

    -- =========================================================================
    --  0. REGISTERS STAGE
    -- =========================================================================

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1') then
                s_data_reg0       <= RX_DATA;
                s_meta_reg0       <= RX_META;
                s_sof_pos_reg0    <= RX_SOF_POS;
                s_eof_pos_reg0    <= slv_array_ser(s_final_eof_pos);
                s_sof_reg0        <= RX_SOF;
                s_eof_reg0        <= s_final_eof;
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_src_rdy_reg0 <= '0';
            elsif (TX_DST_RDY = '1') then
                s_src_rdy_reg0 <= s_src_rdy;
            end if;
        end if;
    end process;

    -- ==========================================================================
    --  TX SIGNALS
    -- ==========================================================================

    TX_DATA        <= s_data_reg0;
    TX_META        <= s_meta_reg0;
    TX_SOF_POS     <= s_sof_pos_reg0;
    TX_EOF_POS     <= s_eof_pos_reg0;
    TX_SOF         <= s_sof_reg0;
    TX_EOF         <= s_eof_reg0;
    TX_SRC_RDY     <= s_src_rdy_reg0;

end architecture;
