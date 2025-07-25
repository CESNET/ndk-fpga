-- testbench.vhd: Testbench for ALU_DSP
-- # Copyright (C) 2014 CESNET
-- # Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
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


    constant CLKPER         : time := 10 ns;           -- Clock period
    constant RESET_TIME     : time := 2*CLKPER + 1 ns; -- Reset durati

    -- Clock and reset signals
    signal clk              : std_logic;
    signal reset            : std_logic;
    signal a                : std_logic_vector(95 downto 0);
    signal b                : std_logic_vector(95 downto 0);
    signal ce_in            : std_logic;
    signal ce_out           : std_logic;
    signal alumode          : std_logic_vector(3 downto 0);
    signal carry_in         : std_logic;
    signal carry_out        : std_logic;
    signal p                : std_logic_vector(95 downto 0);

begin

    uut : entity work.ALU_DSP(structural)
    generic map (
        DATA_WIDTH   => 96,
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
        ALUMODE     => alumode,
        CARRY_IN    => carry_in,
        CARRY_OUT   => carry_out,
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

        carry_in <= '0';
        alumode  <= "0000";
        -- Initialize input interface
        a        <= (others => '0');
        b        <= (others => '0');
        ce_in    <= '0';
        ce_out   <= '0';

        wait for RESET_TIME;
        wait for 3*CLKPER;

        alumode <= "0000";

        a <= (1 => '1', 3 => '1', others => '0');
        b <= (0 => '1', others => '0');
        wait for CLKPER;

        ce_in  <= '1';
        ce_out <= '1';
        wait for CLKPER;

        carry_in <= '1';
        wait for CLKPER;

        carry_in <= '0';
        a        <= (others => '1');
        b        <= (0 => '1', others => '0');
        wait for CLKPER;

        carry_in <= '0';
        a        <= (47 => '1', 94 => '1', others => '0');
        b        <= (47 => '1', 94 => '1', others => '0');
        wait for CLKPER;

        alumode <= "0001";

        a <= (1 => '1', 3 => '1', others => '0');
        b <= (0 => '1', others => '0');
        wait for CLKPER;

        ce_in  <= '1';
        ce_out <= '1';
        wait for CLKPER;

        carry_in <= '1';
        wait for CLKPER;

        carry_in <= '0';
        a        <= (others => '1');
        b        <= (0 => '1', others => '0');
        wait for CLKPER;

        a <= (others => '0');
        b <= (0 => '1', others => '0');
        wait for CLKPER;

        alumode <= "0010";

        a <= (0 => '1', 1 => '1', 2 => '1', 3 => '1', others => '0');
        a <= (0 => '1', 1 => '1', 2 => '1', 3 => '1', 4 => '1', 5 => '1', 6 => '1', 7 => '1', others => '0');
        wait for CLKPER;

        alumode <= "0011";
        wait for CLKPER;

        alumode <= "0100";
        wait for CLKPER;

        alumode <= "0101";
        wait for CLKPER;

        alumode <= "0110";
        wait for CLKPER;

        alumode <= "0111";
        wait for CLKPER;

        alumode <= "1000";
        wait for CLKPER;

        alumode <= "1001";
        wait for CLKPER;

        alumode <= "1010";
        wait for CLKPER;

        alumode <= "1011";
        wait for CLKPER;

        wait;

    end process;

end architecture;
