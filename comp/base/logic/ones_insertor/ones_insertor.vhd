-- ones_insertor.vhd: A component that inserts ones to a vector of zeros from the first Offset to the second Offset.
-- Copyright (C) 2023 CESNET z. s. p. o.
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

-- The output vector has '1's on Items between the first Offset (OFFSET_LOW) and the second Offset (OFFSET_HIGH).
-- Other Items will be 0s.
-- It is expected that OFFSET_LOW < OFFSET_HIGH.
-- When it is not (OFFSET_LOW > OFFSET_HIGH), the output vector will be all 0s.
entity ONES_INSERTOR is
generic(
    -- Width of the Offset signals, max 32 (due to Integer type limit).
    OFFSET_WIDTH : integer := 6
);
port(
    OFFSET_LOW  : in  unsigned(OFFSET_WIDTH-1 downto 0);
    OFFSET_HIGH : in  unsigned(OFFSET_WIDTH-1 downto 0);
    VALID       : in  std_logic := '1';

    ONES_VECTOR : out std_logic_vector(2**OFFSET_WIDTH-1 downto 0)
);
end entity;

architecture FULL of ONES_INSERTOR is

    signal ones_vec1     : std_logic_vector(2**OFFSET_WIDTH-1 downto 0);
    signal ones_vec2     : std_logic_vector(2**OFFSET_WIDTH-1 downto 0);
    signal ones_vec_comb : std_logic_vector(2**OFFSET_WIDTH-1 downto 0);

    signal ptr1 : integer range 2**OFFSET_WIDTH-1 downto 0;
    signal ptr2 : integer range 2**OFFSET_WIDTH-1 downto 0;

begin

    process(all)
    begin
        -- init
        ones_vec1 <= (others => '0');
        ones_vec2 <= (others => '0');

        -- create pointers
        ptr1 <= to_integer(OFFSET_LOW);
        ptr2 <= to_integer(OFFSET_HIGH);

        -- 1st vector: from the MSB to the first Offset
        ones_vec1(2**OFFSET_WIDTH-1 downto ptr1) <= (others => '1');
        -- 2nd vector: from the second Offset to 0
        ones_vec2(ptr2 downto 0) <= (others => '1');
    end process;

    -- vectors combined
    ones_vec_comb <= ones_vec1 and ones_vec2;

    -- final validation
    ONES_VECTOR <= ones_vec_comb and VALID;

end architecture;
