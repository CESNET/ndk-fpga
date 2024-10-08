-- descrambler_gen.vhd : Parellel descrambler for 10/40/100G Ethernet with
--                       generic data width (polynomial: 1 + X^39 + X^58)
--
-- Copyright (C) 201-2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--
-- NOTES:
-- Polynomial
-- +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
-- |Sr0 Sr1 Sr2          ....       Sr38                   Sr57|
-- +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
--  ^                                |                       |
--  |                      D -+---> XOR <--------------------+
--  |                         |      |
--  +-------------------------+      +---> Q

-- Sr0 = D0
-- Sr1 = D1
-- ...
-- Sr57 = D57
--
-- Dout0 = D0 + Sr38 + Sr57
-- Dout1 = D1 + Sr37 + Sr56
-- ...
-- Dout38 = D38 + Sr0 + Sr19  => Dout(i) = Di + Sr(38-i) + Sr(57-i)
-- Dout39 = D39 + D0 + Sr18
-- ...
-- Dout57 = D57 + D(57-39) + Sr0 => Dout(i) = Di + D(i-39) + Sr(57-i)
-- Dout58 = D58 + D(58-39) + D0
-- Dout59 = D59 + D(59-39) + D(59-58) => Dout(i) = Di + D(i-39) + Sr(i-58)
--

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity descrambler_gen is
    generic (
        WIDTH : natural
    );
    port (
        RESET     : in std_logic;
        CLK       : in std_logic; -- Clock, 156.25MHz
        EN        : in std_logic; -- Clock enable
        BYPASS    : in std_logic := '0'; --
        SEED      : in std_logic_vector(57 downto 0);       -- initial seed
        D         : in std_logic_vector(WIDTH-1 downto 0);  -- Input data
        Q         : out std_logic_vector(WIDTH-1 downto 0)  -- Output data
    );
end descrambler_gen;

architecture behavioral of descrambler_gen is

   signal sr   : std_logic_vector(57 downto 0);
   signal din  : std_logic_vector(maximum(WIDTH-1, 57) downto 0) := (others => '0');
   signal dout : std_logic_vector(maximum(WIDTH-1, 57) downto 0);

begin

    din(D'range) <= D;

    GEN_S0_S38: for i in 0 to 38 generate
        dout(i) <= din(i) xor sr(38-i) xor sr(57-i);  -- Dout(i) = Di + Sr(38-i) + Sr(57-i)
    end generate;

    GEN_S39_S57: for i in 39 to 57 generate
        dout(i) <= din(i) xor din(i-39) xor sr(57-i);  -- Dout(i) = Di + D(i-39) + Sr(57-i)
    end generate;

    GEN_S58: for i in 58 to dout'high generate
        dout(i) <= din(i) xor din(i-39) xor din(i-58); -- Dout(i) = Di + D(i-39) + D(i-58)???
    end generate;

    S_SEQ: process(clk, RESET)
    begin
        if CLK'event and CLK = '1' then
            if RESET = '1' then
                sr <= SEED;
            elsif (EN = '1') then
                sr(57 downto WIDTH) <= sr(57-WIDTH downto 0);
                for i in 0 to minimum(WIDTH-1, sr'high) loop
                    sr(i) <= D(WIDTH-1-i);
                end loop;
            end if;
        end if;
    end process;

    Q <= dout(Q'range) when BYPASS = '0' else D;

end behavioral;
