-- scrambler_gen.vhd : Parallel scrambler for 10/40/100G Ethernet (polynomial
--                     1 + X^39 + X^58) with generic data width
-- Copyright (C) 2010-2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--
-- NOTES:
-- Polynomial
-- +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
-- | S0  S1  S2          ....       S38                     S57|
-- +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
--  ^                                |                        |
--  |                       Din ---> + <----------------------+
--  |                                |
--  +--------------------------------+---> Sout

-- S0 = Sr38 + Sr57 + D0
-- S1 = Sr37 + Sr56 + D1
-- ...
-- S38 = Sr0 + Sr19 + D38
-- S39 = Sr(-1) + Sr18 + D39; Sr(-1) = S0
-- S40 = Sr(-2) + Sr17 + D40; Sr(-2) = S1
-- S41 = Sr(-3) + Sr16 + D41; Sr(-3) = S2
-- ...
-- S57 = Sr(-19) + Sr0 + D57; Sr(-19)= S18 = Sr20 + Sr39 + D18
-- S58 = Sr(-20) + Sr(-1) + D58; Sr(-20)= S19 = Sr19 + Sr38 + D19;
-- S59 = Sr(-21) + Sr(-2) + D59;
-- ...
-- Sr(-i) = S(|i|-1)
--
-- In general:
-- Si = Sr(38-i) + Sr(57-i) + Di;  0 <= i <= 38
-- Si = S(i-39) + Sr(57-i) + Di;  39 <= i <= 57
-- Si = S(i-39) + S(i-58) + Di;   58 <= i <= +oo
-- Example: S127 = S(88) + S(69) + D127
-- S(60) = S(60-39) + S(60-58) + D(60) = S(21) +S(2) + D(60) = (Sr17 + Sr36 + D21) + (Sr36 + Sr55 + D2) + D60
--   s_control(60) <= D(60) xor (D(21) xor sr(17)
--     xor sr(36)) xor (D(2) xor sr(36) xor
--     sr(55));

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity scrambler_gen is
    generic (
        WIDTH : natural := 256;
        OREG  : boolean := false
    );
    port (
        RESET     : in std_logic;
        CLK       : in std_logic; -- TX clock, 156.25MHz
        EN        : in std_logic; -- Clock enable
        BYPASS    : in std_logic := '0';
        SEED      : in std_logic_vector(57 downto 0);  -- initial seed
        D         : in std_logic_vector(WIDTH-1 downto 0);   -- Input data
        Q         : out std_logic_vector(WIDTH-1 downto 0) := (others => '0') -- Output data
    );
end scrambler_gen;

architecture behavioral of scrambler_gen is

    signal sr  : bit_vector(57 downto 0) := (others => '0');
    signal s   : std_logic_vector(maximum(WIDTH-1, 57) downto 0);
    signal din : std_logic_vector(maximum(WIDTH-1, 57) downto 0) := (others => '0');

begin

    din(D'range) <= D;

    GEN_S0_S38: for i in 0 to 38 generate
        s(i) <= din(i) xor To_X01(sr(38-i)) xor To_X01(sr(57-i));
    end generate;

    GEN_S39_S57: for i in 39 to 57 generate
        s(i) <= din(i) xor s(i-39) xor To_X01(sr(57-i));
    end generate;

    GEN_S58: for i in 58 to s'high generate
        s(i) <= din(i) xor s(i-39) xor s(i-58);
    end generate;

    S_SEQ: process(clk, reset)
    begin
        if CLK'event and CLK = '1' then
            if RESET = '1' then
                sr <= to_bitvector(SEED);
            elsif (EN = '1') then
                sr(57 downto WIDTH) <= sr(57-WIDTH downto 0);
                for i in 0 to minimum(WIDTH-1, sr'high) loop
                    sr(i) <= to_bit(s(WIDTH-1-i));
                end loop;
            end if;
        end if;
    end process;

    GEN_NO_OREG: if (not OREG) generate
        Q <= s(Q'range) when BYPASS = '0' else D;
    end generate;

    GEN_OREG: if (OREG) generate

        OREG_FF: process(CLK)
        begin
            if CLK'event and CLK = '1' then
                if (EN = '1') then
                    if (BYPASS = '0') then
                        Q <= s(Q'range);
                    else
                        Q <= D;
                    end if;
                end if;
            end if;
        end process;

    end generate;


end behavioral;
