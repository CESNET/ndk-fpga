--! testbench.vhd: Testbench for PIPE
--! Copyright (C) 2015 CESNET
--! Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--!
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


    constant CLKPER           : time := 10 ns;           -- Clock period
    constant RESET_TIME       : time := 2*CLKPER + 1 ns; -- Reset durati
    --! generic parameters
    constant DATA_WIDTH       : integer := 20;
    constant NUM_REGS         : integer := 1;
    --! Clock and reset signals
    signal   clk              : std_logic;
    signal   reset            : std_logic;
    --! input and output
    signal   data_in          : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal   data_out         : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal   ce               : std_logic;

begin

    uut: entity work.PIPE_DSP
    generic map (
        DATA_WIDTH => DATA_WIDTH,
        NUM_REGS   => NUM_REGS,
        ENABLE_DSP => true,
        PIPE_EN    => false
    )
    port map (
        CLK      => clk,
        RESET    => reset,
        DATA_IN  => data_in,
        DATA_OUT => data_out,
        CE       => ce
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
        data_in <= (others => '0');
        ce      <= '1';

        wait for RESET_TIME;
        wait for 3*CLKPER;
        wait for CLKPER;

        data_in <= conv_std_logic_vector(1, data_in'LENGTH);
        wait for CLKPER;

        data_in <= conv_std_logic_vector(2, data_in'LENGTH);
        wait for CLKPER;

        data_in <= conv_std_logic_vector(3, data_in'LENGTH);
        wait for CLKPER;

        wait;

    end process;
end architecture;
