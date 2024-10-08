-- offset_reached.vhd:
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

-- This unit searches for an Item given by the input Offset across Regions and Words.
-- Each OFFSET_REACHED unit serches in its Region specified by the REGION_NUMBER.
-- When it finds (reaches) the target Item, it outputs '1'.
entity OFFSET_REACHED is
generic(
    MAX_WORDS     : natural := 150;
    OFFSET_WIDTH  : natural := 15;

    REGIONS       : natural := 4;
    REGION_ITEMS  : natural := 64;
    REGION_NUMBER : natural := 0
);
port(
    -- The number of the current word from SOF.
    -- Each Sof should reset this count, but beware situation
    -- where the Offset points to an Item in the same Region as is a SOF of a following packet.
    RX_WORD   : in  unsigned(log2(MAX_WORDS)-1 downto 0);
    -- Number of Items from the start of the word, in which the Offset is received.
    -- When receiving an Offset that starts from SOF ("SOF Offset"),
    -- convert it to Offset from the start of the word ("Global Offset")
    -- by adding SOFPOS to the number of Items in the previous Regions.
    RX_OFFSET : in  unsigned(OFFSET_WIDTH-1 downto 0);
    -- Valid for the Offset.
    RX_VALID  : in  std_logic;

    -- Is '1' when the target Item given by the Offset is in this Word and Region.
    -- The target Item is given by the lower bits of the Offset signal.
    TX_REACHED : out std_logic
);
end entity;

architecture FULL of OFFSET_REACHED is

    constant WORDS_WIDTH  : natural := OFFSET_WIDTH - log2(REGIONS*REGION_ITEMS);

    signal target_word    : unsigned(WORDS_WIDTH-1 downto 0);
    signal target_region  : unsigned(log2(REGIONS)-1 downto 0);
    signal offset_reached : std_logic;

begin

    assert (log2(MAX_WORDS) >= WORDS_WIDTH)
        report "MFB OFFSET REACHED: the value of the MAX_WORDS generic is too small (=" & integer'image(MAX_WORDS) & ")!"
        severity failure;

    target_word   <= RX_OFFSET(OFFSET_WIDTH            -1 downto OFFSET_WIDTH-WORDS_WIDTH              );
    target_region <= RX_OFFSET(OFFSET_WIDTH-WORDS_WIDTH-1 downto OFFSET_WIDTH-WORDS_WIDTH-log2(REGIONS));

    regions_g : if REGIONS > 1 generate
        offset_reached <= '1' when (RX_WORD(WORDS_WIDTH-1 downto 0) = target_word) and (REGION_NUMBER = target_region) else '0';
    else generate
        offset_reached <= '1' when (RX_WORD(WORDS_WIDTH-1 downto 0) = target_word) else '0';
    end generate;

    TX_REACHED <= offset_reached and RX_VALID;

end architecture;
