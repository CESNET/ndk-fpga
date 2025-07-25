-- testbench.vhd: Testbench for XOR48
-- Copyright (C) 2013 CESNET
-- Author: Viktor Pus <pus@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

entity TESTBENCH is

end entity;

architecture BEHAVIORAL of TESTBENCH is


    constant CLKPER         : time := 10 ns;            -- Clock period
    constant RESET_TIME     : time := 10*CLKPER + 1 ns; -- Reset duration

    -- Clock and reset signals
    signal clk              : std_logic;
    signal reset            : std_logic;

    -- input and output
    signal a                : std_logic_vector(47 downto 0);
    signal b                : std_logic_vector(47 downto 0);
    signal ceab             : std_logic;
    signal cep              : std_logic;
    signal p                : std_logic_vector(47 downto 0);

begin

    -- XOR48
    uut : entity work.XOR48(V7_DSP)
    generic map (
        ABREG       => 1,
        PREG        => 1
    )
    port map (
        CLK         => clk,
        RESET       => reset,

        A           => a,
        B           => b,
        CEAB        => ceab,
        CEP         => cep,
        P           => p
    );

    -- Generate clock
    clk_gen_p : process
    begin
        clk <= '1';
        wait for CLKPER/2;
        clk <= '0';
        wait for CLKPER/2;
    end process;

    -- Generate reset
    reset_gen : process
    begin
        reset <= '1';
        wait for RESET_TIME;
        reset <= '0';
        wait;
    end process;

    -- Simulating input flow
    input_flow : process
    begin

        -- Initialize input interface
        a    <= X"000000000000";
        b    <= X"000000000000";
        ceab <= '1';
        cep  <= '1';

        wait for RESET_TIME;
        wait for 10*CLKPER;

        a <= X"00FF00FF00FF";
        b <= X"0F0F0F0F0F0F";
        wait for CLKPER;

        a <= X"0123456789AB";
        b <= X"FEDCBA987654";
        wait for CLKPER;

        a <= X"0123456789AB";
        b <= X"0123456789AB";
        wait for CLKPER;

        a <= X"EDCBA9876543";
        b <= X"FEDCBA987654";
        wait for CLKPER;

        wait;

    end process;

end architecture;
