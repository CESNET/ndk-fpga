-- testbench.vhd: glitch filter testbench file
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <Pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_arith.all;

library work;
use work.math_pack.all;

entity TESTBENCH is
end entity;

architecture TESTBENCH of TESTBENCH is

    constant CLKPER         : time      := 10 ns;
    constant RESET_TIME     : time      := 10*CLKPER + 1 ns;

    signal clk           : std_logic;
    signal reset         : std_logic;

    signal din           : std_logic;
    signal dout          : std_logic;

begin

    uut: entity work.GLITCH_FILTER
    generic map (
        FILTER_LENGTH   => 8,
        FILTER_SAMPLING => 2,
        INIT            => '1'
    )
    port map (
        CLK            => clk,
        RESET          => reset,
        --
        DIN            => din,
        DOUT           => dout
    );

    clkgen : process
    begin
        clk <= '1';
        wait for CLKPER/2;
        clk <= '0';
        wait for CLKPER/2;
    end process;

    reset_gen : process
    begin
        reset <= '1';
        wait for RESET_TIME;
        reset <= '0';
        wait;
    end process;

    tb_main : process
    begin
        din <= '0';
        wait for RESET_TIME;

        wait for 20*CLKPER;
        din <= '1';
        wait for 8*CLKPER;
        din <= '0';
        wait for 8*CLKPER;
        din <= '1';

        wait;
    end process;


end architecture;
