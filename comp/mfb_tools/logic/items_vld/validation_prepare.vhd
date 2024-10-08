-- validation_prepare.vhd: A component that processes Offsets and Lengths in order to select those for the actual validation process.
-- Copyright (C) 2023 CESNET z.s.p.o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.type_pack.all;
use work.math_pack.all;


-- ============================================================================
-- Description
-- ============================================================================

-- This component prepares the Offsets and Lengths for the next stage, where the validation is actually performed.
-- The preparation is about converting the Offsets that are from SOF POS to be from the beginning of the current word.
-- When the Offset is reached (Word and Region), the Offset gets rounded up to the following Region.
-- And also, the Length is decremented by the number of Items that are from the Offset to the end of the Region.
entity VALIDATION_PREPARE is
generic(
    -- Number of Regions within a data word, must be power of 2.
    MFB_REGIONS     : natural := 4;
    -- Region size (in Blocks).
    MFB_REGION_SIZE : natural := 8;
    -- Block size (in Items).
    MFB_BLOCK_SIZE  : natural := 8;

    -- Maximum amount of Words a single packet can stretch over.
    MAX_WORDS       : natural := 10;
    -- Width of the Offset signals.
    OFFSET_WIDTH    : integer := log2(MAX_WORDS*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)
);
port(
    -- ========================================================================
    -- Clock and Reset
    -- ========================================================================

    CLK             : in  std_logic;
    RESET           : in  std_logic;

    -- ========================================================================
    -- RX inf
    -- ========================================================================

    -- Number of the current word (counted from each SOF).
    RX_WORD         : in  u_array_t       (MFB_REGIONS-1 downto 0)(log2(MAX_WORDS)-1 downto 0);
    RX_WORD_PREV    : in  u_array_t       (MFB_REGIONS-1 downto 0)(log2(MAX_WORDS)-1 downto 0);
    -- Offset of the Start of the Section-to-be-validated (from the beginning of the word; in Items).
    RX_OFFSET_START : in  u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    -- Offset of the End of the Section-to-be-validated (from the beginning of the word; in Items).
    RX_OFFSET_END   : in  u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    RX_VALID        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_SRC_RDY      : in  std_logic;
    RX_DST_RDY      : out std_logic;

    -- ========================================================================
    -- TX inf
    -- ========================================================================

    -- With current SOF
    TX_OFFSET1_START : out u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    TX_OFFSET1_END   : out u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    TX_VALID1        : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_END1_POINTER  : out u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    TX_END1          : out std_logic_vector(MFB_REGIONS-1 downto 0);

    -- With older SOF
    TX_OFFSET2_START : out u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    TX_OFFSET2_END   : out u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    TX_VALID2        : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_END2_POINTER  : out u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    TX_END2          : out std_logic_vector(MFB_REGIONS-1 downto 0);

    TX_SRC_RDY       : out std_logic;
    TX_DST_RDY       : in  std_logic
);
end entity;

architecture FULL of VALIDATION_PREPARE is

    -- ========================================================================
    --                                CONSTANTS
    -- ========================================================================

    -- Number of Blocks and Items in a Region.
    constant REGION_ITEMS   : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    constant REGION_ITEMS_W : natural := log2(REGION_ITEMS);

    -- ========================================================================
    --                                 SIGNALS
    -- ========================================================================

    signal start_reached1         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal end_reached1           : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal vp_rx_word             : u_array_t       (MFB_REGIONS-1 downto 0)(log2(MAX_WORDS)-1 downto 0);
    signal vp_rx_word_prev        : u_array_t       (MFB_REGIONS-1 downto 0)(log2(MAX_WORDS)-1 downto 0);
    signal vp_rx_new_offset_start : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    signal vp_rx_new_offset_end   : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    signal vp_rx_new_valid        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal vp_rx_old_offset_start : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    signal vp_rx_old_offset_end   : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    signal vp_rx_old_valid        : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal vp_tx_offset_start     : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    signal vp_tx_offset_end       : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    signal vp_tx_valid            : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal start_reached2         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal end_reached2           : std_logic_vector(MFB_REGIONS-1 downto 0);

begin

    RX_DST_RDY <= TX_DST_RDY;

    -- ========================================================================
    -- Prepare logic 1
    -- ========================================================================

    -- ------------------------
    --  Evaluate input Offsets
    -- ------------------------
    offset_reached1_g : for r in 0 to MFB_REGIONS-1 generate

        offset_start_reached1_i : entity work.OFFSET_REACHED
        generic map(
            MAX_WORDS     => MAX_WORDS    ,
            OFFSET_WIDTH  => OFFSET_WIDTH ,
            REGIONS       => MFB_REGIONS  ,
            REGION_ITEMS  => REGION_ITEMS ,
            REGION_NUMBER => r
        )
        port map(
            RX_WORD    => RX_WORD        (r),
            RX_OFFSET  => RX_OFFSET_START(r),
            RX_VALID   => RX_VALID       (r),

            TX_REACHED => start_reached1 (r)
        );

        offset_end_reached1_i : entity work.OFFSET_REACHED
        generic map(
            MAX_WORDS     => MAX_WORDS    ,
            OFFSET_WIDTH  => OFFSET_WIDTH ,
            REGIONS       => MFB_REGIONS  ,
            REGION_ITEMS  => REGION_ITEMS ,
            REGION_NUMBER => r
        )
        port map(
            RX_WORD    => RX_WORD      (r),
            RX_OFFSET  => RX_OFFSET_END(r),
            RX_VALID   => RX_VALID     (r),

            TX_REACHED => end_reached1 (r)
        );

    end generate;

    -- ========================================================================
    -- Prepare logic 2
    -- ========================================================================

    vp_rx_word             <= RX_WORD;
    vp_rx_word_prev        <= RX_WORD_PREV;
    vp_rx_new_offset_start <= RX_OFFSET_START;
    vp_rx_new_offset_end   <= RX_OFFSET_END;
    vp_rx_new_valid        <= RX_VALID;

    -- --------------------------------------------
    --  Process the input as well as older Offsets
    -- --------------------------------------------
    validation_prepare_r_g : for r in 0 to MFB_REGIONS-1 generate
        validation_prepare_r_i : entity work.VALIDATION_PREPARE_R
        generic map(
            MFB_REGIONS     => MFB_REGIONS    ,
            MFB_REGION_SIZE => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE ,
            REGION_NUMBER   => r              ,
            MAX_WORDS       => MAX_WORDS      ,
            OFFSET_WIDTH    => OFFSET_WIDTH
        )
        port map(
            RX_WORD             => vp_rx_word            (r),
            RX_WORD_PREV        => vp_rx_word_prev       (r),
            RX_NEW_OFFSET_START => vp_rx_new_offset_start(r),
            RX_NEW_OFFSET_END   => vp_rx_new_offset_end  (r),
            RX_NEW_VALID        => vp_rx_new_valid       (r),
            RX_OLD_OFFSET_START => vp_rx_old_offset_start(r),
            RX_OLD_OFFSET_END   => vp_rx_old_offset_end  (r),
            RX_OLD_VALID        => vp_rx_old_valid       (r),

            TX_OFFSET_START => vp_tx_offset_start(r),
            TX_OFFSET_END   => vp_tx_offset_end  (r),
            TX_VALID        => vp_tx_valid       (r)
        );
    end generate;

    -- -------------------------
    --  Propagate vp_tx signals
    -- -------------------------
    propagate_signals_g : for r in 0 to MFB_REGIONS-2 generate
        vp_rx_old_offset_start(r+1) <= vp_tx_offset_start(r);
        vp_rx_old_offset_end  (r+1) <= vp_tx_offset_end  (r);
        vp_rx_old_valid       (r+1) <= vp_tx_valid       (r);
    end generate;

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (RX_SRC_RDY = '1') and (TX_DST_RDY = '1') then
                vp_rx_old_offset_start(0) <= vp_tx_offset_start(MFB_REGIONS-1);
                vp_rx_old_offset_end  (0) <= vp_tx_offset_end  (MFB_REGIONS-1);
                vp_rx_old_valid       (0) <= vp_tx_valid       (MFB_REGIONS-1);
            end if;
            if (RESET = '1') then
                vp_rx_old_valid(0) <= '0';
            end if;
        end if;
    end process;

    -- ------------------------
    --  Evaluate older Offsets
    -- ------------------------
    offset_reached2_g : for r in 0 to MFB_REGIONS-1 generate

        offset_start_reached2_i : entity work.OFFSET_REACHED
        generic map(
            MAX_WORDS     => MAX_WORDS    ,
            OFFSET_WIDTH  => OFFSET_WIDTH ,
            REGIONS       => MFB_REGIONS  ,
            REGION_ITEMS  => REGION_ITEMS ,
            REGION_NUMBER => r
        )
        port map(
            RX_WORD    => vp_rx_word_prev       (r),
            RX_OFFSET  => vp_rx_old_offset_start(r),
            RX_VALID   => vp_rx_old_valid       (r),

            TX_REACHED => start_reached2        (r)
        );

        offset_end_reached2_i : entity work.OFFSET_REACHED
        generic map(
            MAX_WORDS     => MAX_WORDS    ,
            OFFSET_WIDTH  => OFFSET_WIDTH ,
            REGIONS       => MFB_REGIONS  ,
            REGION_ITEMS  => REGION_ITEMS ,
            REGION_NUMBER => r
        )
        port map(
            RX_WORD    => vp_rx_word_prev     (r),
            RX_OFFSET  => vp_rx_old_offset_end(r),
            RX_VALID   => vp_rx_old_valid     (r),

            TX_REACHED => end_reached2        (r)
        );

    end generate;

    -- ========================================================================
    -- Output assignment
    -- ========================================================================

    output_g : for r in 0 to MFB_REGIONS-1 generate
        TX_OFFSET1_START(r) <= RX_OFFSET_START       (r)(REGION_ITEMS_W-1 downto 0);
        TX_OFFSET1_END  (r) <= RX_OFFSET_END         (r)(REGION_ITEMS_W-1 downto 0) when (end_reached1(r) = '1') else (others => '1');
        TX_VALID1       (r) <= start_reached1        (r);
        TX_END1_POINTER (r) <= RX_OFFSET_END         (r)(REGION_ITEMS_W-1 downto 0);
        TX_END1         (r) <= end_reached1          (r);

        TX_OFFSET2_START(r) <= vp_rx_old_offset_start(r)(REGION_ITEMS_W-1 downto 0);
        TX_OFFSET2_END  (r) <= vp_rx_old_offset_end  (r)(REGION_ITEMS_W-1 downto 0) when (end_reached2(r) = '1') else (others => '1');
        TX_VALID2       (r) <= start_reached2        (r);
        TX_END2_POINTER (r) <= vp_rx_old_offset_end  (r)(REGION_ITEMS_W-1 downto 0);
        TX_END2         (r) <= end_reached2          (r);
    end generate;

    TX_SRC_RDY <= RX_SRC_RDY;

end architecture;
