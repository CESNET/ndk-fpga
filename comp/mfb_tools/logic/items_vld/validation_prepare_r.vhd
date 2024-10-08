-- validation_prepare.vhd: A component that selects, updates, and outputs valid Offsets and Lengths (per Region).
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
--  Description
-- ============================================================================

-- A simple Regional component that searches for the Offset (identifying the Start Of The Section)
-- and updates it as well as the Length signal, if it finds it.
-- If it finds the End Of The Section, it invalidates the Offset and Length signals.
entity VALIDATION_PREPARE_R is
generic(
    -- Number of Regions within a data word, must be power of 2.
    MFB_REGIONS     : natural := 4;
    -- Region size (in Blocks).
    MFB_REGION_SIZE : natural := 8;
    -- Block size (in Items).
    MFB_BLOCK_SIZE  : natural := 8;

    -- Instance ID - corresponds with the Region it is in.
    REGION_NUMBER   : natural := 0;

    -- Maximum amount of Words a single packet can stretch over.
    MAX_WORDS       : natural := 100;
    -- Width of the Offset signals.
    OFFSET_WIDTH    : integer := log2(MAX_WORDS*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)
);
port(
    -- ========================================================================
    -- RX_NEW inf: connected to the input MFB interface (2 levels above).
    --
    -- RX_OLD inf: connected to the previous VALIDATION_PREPARE_R.
    -- ========================================================================

    -- Number of the current word (counted from each SOF).
    RX_WORD             : in  unsigned(log2(MAX_WORDS)-1 downto 0);
    -- Number of the previous word (counted from each SOF but in the previous Region).
    RX_WORD_PREV        : in  unsigned(log2(MAX_WORDS)-1 downto 0);

    -- Offset of the Start of the Section-to-be-validated from the beginning of the word (in Items).
    RX_NEW_OFFSET_START : in  unsigned(OFFSET_WIDTH-1 downto 0);
    -- Offset of the End of the Section-to-be-validated from the beginning of the word (in Items).
    RX_NEW_OFFSET_END   : in  unsigned(OFFSET_WIDTH-1 downto 0);
    -- Valid for the RX_NEW signals.
    RX_NEW_VALID        : in  std_logic;

    -- Offset of the Start of the Section-to-be-validated from the beginning of the word (in Items).
    RX_OLD_OFFSET_START : in  unsigned(OFFSET_WIDTH-1 downto 0);
    -- Offset of the End of the Section-to-be-validated from the beginning of the word (in Items).
    RX_OLD_OFFSET_END   : in  unsigned(OFFSET_WIDTH-1 downto 0);
    -- Valid for the RX_OLD signals.
    RX_OLD_VALID        : in  std_logic;

    -- ========================================================================
    -- TX inf
    -- ========================================================================

    TX_OFFSET_START : out unsigned(OFFSET_WIDTH-1 downto 0);
    TX_OFFSET_END   : out unsigned(OFFSET_WIDTH-1 downto 0);
    TX_VALID        : out std_logic
);
end entity;

architecture FULL of VALIDATION_PREPARE_R is

    -- ========================================================================
    --                                CONSTANTS
    -- ========================================================================

    -- Number of Blocks and Items in a Region.
    constant REGION_ITEMS   : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    constant REGION_ITEMS_W : natural := log2(REGION_ITEMS);
    -- MAX_REGIONS = maximum amount of Regions (possibly across multiple words) a single packet can strech over.
    constant MAX_REGIONS_W  : natural := max(0, OFFSET_WIDTH - REGION_ITEMS_W);

    -- ========================================================================
    --                                 SIGNALS
    -- ========================================================================

    signal rx_valid_input           : std_logic;
    signal rx_selected_offset_start : unsigned(OFFSET_WIDTH-1 downto 0);
    signal rx_selected_offset_end   : unsigned(OFFSET_WIDTH-1 downto 0);
    signal offset_word_and_region   : unsigned(MAX_REGIONS_W-1 downto 0);
    signal updated_offset           : unsigned(OFFSET_WIDTH-1 downto 0);
    signal section_start            : std_logic;
    signal RX_WORD_end              : unsigned(log2(MAX_WORDS)-1 downto 0);
    signal section_end              : std_logic;
    signal tx_selected_offset_start : unsigned(OFFSET_WIDTH-1 downto 0);

begin

    rx_valid_input <= RX_NEW_VALID or RX_OLD_VALID;

    -- ------------------------------------
    --  Select the input Offset and Length
    -- ------------------------------------
    rx_selected_offset_start <= RX_NEW_OFFSET_START when (RX_NEW_VALID = '1') else RX_OLD_OFFSET_START;
    rx_selected_offset_end   <= RX_NEW_OFFSET_END   when (RX_NEW_VALID = '1') else RX_OLD_OFFSET_END;

    -- --------------------------
    --  Update Offset and Length
    -- --------------------------
    -- Round up the Offset to the next Region
    offset_word_and_region <= rx_selected_offset_start(OFFSET_WIDTH-1 downto REGION_ITEMS_W);
    updated_offset <= resize_right(offset_word_and_region + to_unsigned(1, MAX_REGIONS_W), OFFSET_WIDTH); -- Add overflow detection?

    -- ----------------------
    --  Evaluate the Offsets
    -- ----------------------
    offset_start_reached_i : entity work.OFFSET_REACHED
    generic map(
        MAX_WORDS     => MAX_WORDS    ,
        REGIONS       => MFB_REGIONS  ,
        REGION_ITEMS  => REGION_ITEMS ,
        OFFSET_WIDTH  => OFFSET_WIDTH ,
        REGION_NUMBER => REGION_NUMBER
    )
    port map(
        RX_WORD    => RX_WORD                 ,
        RX_OFFSET  => rx_selected_offset_start,
        RX_VALID   => rx_valid_input          ,

        TX_REACHED => section_start
    );

    RX_WORD_end <= RX_WORD         when (RX_NEW_VALID = '1') else
                   RX_WORD_PREV    when (RX_OLD_VALID = '1') else
                   (others => '0');

    offset_end_reached_i : entity work.OFFSET_REACHED
    generic map(
        MAX_WORDS     => MAX_WORDS    ,
        REGIONS       => MFB_REGIONS  ,
        REGION_ITEMS  => REGION_ITEMS ,
        OFFSET_WIDTH  => OFFSET_WIDTH ,
        REGION_NUMBER => REGION_NUMBER
    )
    port map(
        RX_WORD    => RX_WORD_end           ,
        RX_OFFSET  => rx_selected_offset_end,
        RX_VALID   => rx_valid_input        ,

        TX_REACHED => section_end
    );

    -- -----------------------------
    --  Select the Offset to output
    -- -----------------------------
    tx_selected_offset_start <= updated_offset when (section_start = '1') else rx_selected_offset_start;

    -- -------------------
    --  Output assignment
    -- -------------------
    TX_OFFSET_START <= tx_selected_offset_start;
    TX_OFFSET_END   <= rx_selected_offset_end;
    TX_VALID        <= rx_valid_input and not section_end;

end architecture;
