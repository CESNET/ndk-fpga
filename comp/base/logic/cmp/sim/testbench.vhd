--! testbench.vhd: Testbench for CMP48
--! # Copyright (C) 2014 CESNET
--! # Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
--! SPDX-License-Identifier: BSD-3-Clause
--
--! $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

entity TESTBENCH is

end entity;

architecture BEHAVIORAL of TESTBENCH is


    constant CLKPER         : time := 10 ns;           -- Clock period
    constant RESET_TIME     : time := 2*CLKPER + 1 ns; -- Reset durati

    --! Clock and reset signals
    signal clk              : std_logic;
    signal reset            : std_logic;

    --! input and output
    signal a                : std_logic_vector(129 downto 0);
    signal b                : std_logic_vector(129 downto 0);
    signal ce_in            : std_logic;
    signal ce_out           : std_logic;
    signal p                : std_logic_vector(1 downto 0);

begin

    --! CMP48
    uut : entity work.CMP_DSP(structural)
    generic map (
        DATA_WIDTH   => 130,
        REG_IN       => 1,
        REG_OUT      => 1
    )
    port map (
        CLK         => clk,
        RESET       => reset,
        A           => a,
        B           => b,
        CE_IN       => ce_in,
        CE_OUT      => ce_out,
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

    --! Simulating input flow
    input_flow : process
    begin

        --! Initialize input interface
        a      <= (others => '0');
        b      <= (others => '0');
        ce_in  <= '0';
        ce_out <= '0';

        wait for RESET_TIME;
        wait for 3*CLKPER;
        wait for CLKPER;

        a <= (24 => '0', others => '1');
        b <= (others => '1');
        wait for CLKPER;

        ce_in  <= '1';
        ce_out <= '1';
        wait for CLKPER;

        a <= (  105 => '1', 84 => '0', 1 => '1', 30 => '0', others => '0');
        b <= (  105 => '1', 84 => '1', 1 => '1', 30 => '0', others => '0');
        wait for CLKPER;

        a <= (  105 => '1', 84 => '1', 1 => '1', 30 => '0', others => '0');
        b <= (  105 => '1', 84 => '1', 1 => '1', 30 => '0', others => '0');
        wait for CLKPER;

        a <= (  105 => '1', 84 => '1', 1 => '1', 30 => '0', others => '0');
        b <= (  105 => '1', 84 => '1', 0 => '1', 30 => '0', others => '0');
        wait for CLKPER;

        a <= (  105 => '0', 84 => '1', 1 => '1', 30 => '0', others => '0');
        b <= (  105 => '1', 84 => '1', 0 => '1', 30 => '0', others => '0');
        wait for CLKPER;

        a <= (  105 => '1', 84 => '1', 45 => '1', 30 => '1', others => '0');
        b <= (  105 => '1', 84 => '1', 45 => '1', 30 => '1', others => '0');
        wait for CLKPER;

        wait;

    end process;
end architecture;
