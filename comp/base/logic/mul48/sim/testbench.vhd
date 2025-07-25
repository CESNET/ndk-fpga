-- testbench.vhd: Testbench for MUL48
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
    constant A_DATA_WIDTH   : integer := 17;
    constant B_DATA_WIDTH   : integer := 143;

    -- Clock and reset signals
    signal clk              : std_logic;
    signal reset            : std_logic;

    -- input and output
    signal a                : std_logic_vector(A_DATA_WIDTH-1 downto 0);
    signal b                : std_logic_vector(B_DATA_WIDTH-1 downto 0);
    signal ce               : std_logic;
    signal p                : std_logic_vector(A_DATA_WIDTH+B_DATA_WIDTH-1 downto 0);

begin

    -- MUL48
    uut : entity work.MUL_DSP
    generic map (
        A_DATA_WIDTH => A_DATA_WIDTH,
        B_DATA_WIDTH => B_DATA_WIDTH,
        REG_IN       => 1,
        REG_OUT      => 1
    )
    port map (
        CLK         => clk,
        RESET       => reset,
        A           => a,
        B           => b,
        CE          => ce,
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
        a  <= (others => '0');
        b  <= (others => '0');
        ce <= '1';

        wait for RESET_TIME;
        wait for 3*CLKPER;
        wait for CLKPER;

        a  <= (others => '1');
        b  <= (others => '1');
        wait for CLKPER;
        wait for CLKPER;
        wait for CLKPER;
        ce <= '0';
        wait for 20*CLKPER;
        ce <= '1';

        wait;

    end process;

end architecture;
