-- testbench.vhd: Testbench for COUNT48
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
    constant WIDTH          : integer := 128;

    constant CLKPER         : time := 5 ns;            -- Clock period
    constant RESET_TIME     : time := 2*CLKPER + 1 ns; -- Reset durati

    -- Clock and reset signals
    signal clk              : std_logic;
    signal reset            : std_logic;
    -- input and output:
    signal a                : std_logic_vector(WIDTH-1 downto 0);
    signal max              : std_logic_vector(WIDTH-1 downto 0);
    signal enable           : std_logic;
    signal p                : std_logic_vector(WIDTH-1 downto 0);

begin

    -- COUNT48
    uut : entity work.COUNT_DSP(structural)
    generic map (
        DATA_WIDTH => width,
        REG_IN     => 1,
        AUTO_RESET => 0,
        DSP_EN     => false
    )
    port map (
        CLK         => clk,
        RESET       => reset,
        A           => a,
        MAX         => max,
        ENABLE      => enable,
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

        enable <= '0';
        -- MAX <= (95 => '1', 46 => '1', others => '1');
        -- A <= (49 => '1', 46 => '1', others => '0');
        max    <= (  50 => '1', 53 => '1', 46 => '1', 49 => '1', others => '0');
        a      <= (   60 => '1', 53 => '0', 46 => '1', 49 => '0', others => '0');
        wait for RESET_TIME;
        wait for 2*CLKPER;

        enable <= '1';
        wait for CLKPER;

        enable <= '0';
        wait for CLKPER;

        enable <= '1';
        wait for 2*CLKPER;

        enable <= '0';
        wait for CLKPER;

        --  A <= (1 => '1', others => '0');
        enable <= '0';
        wait for 6*CLKPER;

        enable <= '1';
        wait for 2*CLKPER;

        enable <= '0';
        wait for 2*CLKPER;

        enable <= '1';
        wait;

    end process;

end architecture;
