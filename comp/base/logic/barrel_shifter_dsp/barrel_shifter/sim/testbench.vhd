-- testbench.vhd: Testbench for BAREL_SHIFTER_DSP_TOP
-- # Copyright (C) 2015 CESNET
-- # Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;
entity TESTBENCH is

end entity;

architecture BEHAVIORAL of TESTBENCH is

    constant CLKPER           : time := 10 ns;           -- Clock period
    constant RESET_TIME       : time := 2*CLKPER + 1 ns; -- Reset durati
    constant WIDTH            : integer := 8;
    constant WIDTH_SHIFT      : integer := 4;
    -- Clock and reset signals
    signal   clk              : std_logic;
    signal   reset            : std_logic;

    -- input and output
    signal data_in          : std_logic_vector(WIDTH-1 downto 0);
    signal data_out         : std_logic_vector(WIDTH-1 downto 0);
    signal shift_exp        : std_logic_vector(WIDTH_SHIFT-1 downto 0);
    signal shift_binary     : std_logic_vector(log2(WIDTH_SHIFT)-1 downto 0);
    signal ce_in            : std_logic;
    signal ce_out           : std_logic;

begin

    -- DSP_SHIFTER
    uut : entity work.BARREL_SHIFTER_DSP(shift_arch)
    generic map (
        DATA_WIDTH       => WIDTH,
        SHIFT_LEFT       => true,
        REG_IN           => 1,
        REG_OUT          => 1,
        REGS_WITH_DSP    => true,
        MAX_SHIFT        => WIDTH_SHIFT,
        SEL_FORMAT_SHIFT => 0
    )
    port map (
        CLK            => clk,
        RESET          => reset,
        DATA_IN        => data_in,
        DATA_OUT       => data_out,
        SHIFT_EXP      => shift_exp,
        SHIFT_BINARY   => shift_binary,
        CE_IN          => '1',
        CE_OUT         => '1'
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
        data_in      <= (others => '0');
        shift_exp    <= (others => '0');
        shift_binary <= (others => '0');
        ce_in        <= '1';
        ce_out       <= '1';

        wait for RESET_TIME;
        wait for 2*CLKPER;

        data_in   <= X"0F";
        shift_exp <= (others => '0');
        wait for CLKPER;

        shift_exp    <= (0 => '1', others => '0');
        shift_binary <= conv_std_logic_vector(1, shift_binary'LENGTH);
        wait for CLKPER;

        shift_exp    <= (1 => '1', others => '0');
        shift_binary <= conv_std_logic_vector(2, shift_binary'LENGTH);
        wait for CLKPER;

        shift_exp    <= (2 => '1', others => '0');
        shift_binary <= conv_std_logic_vector(3, shift_binary'LENGTH);
        wait for CLKPER;

        shift_exp    <= (3 => '1', others => '0');
        shift_binary <= conv_std_logic_vector(4, shift_binary'LENGTH);
        wait for CLKPER;

        wait;
    end process;

end architecture;
