-- testbench.vhd: Testbench for xor8x12
-- Copyright (C) 2018 CESNET
-- Author: Petr Panak <xpanak04@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_misc.all;

entity TESTBENCH is

end entity;

architecture BEHAVIORAL of TESTBENCH is

    constant CLKPER      : time := 10 ns;              -- Clock period
    constant RESET_TIME  : time := 10*CLKPER + 1 ns;   -- Reset duration

    -- Clock and reset signals
    signal clk           : std_logic;
    signal reset         : std_logic;

    -- Input and output signals
    signal di         : std_logic_vector(95 downto 0);    -- Data input
    signal do_8x12    : std_logic_vector(7 downto 0);     -- Data output for 8x12-bit xor
    signal cei        : std_logic;                        -- Clock enable for input registers
    signal ceo        : std_logic;                        -- Clock enable for output registers

    -- Signals for verification of xor function
    signal d_8x12     : std_logic_vector(7 downto 0);

begin
    -- xor8x12 entity
    uut : entity work.XOR8X12(VU_DSP)
    generic map (
        IREG       => 0,
        OREG       => 0
    )
    port map (
        CLK         => clk,
        RESET       => reset,

        DI          => di,
        CEI         => cei,
        CEO         => ceo,
        DO_8x12     => do_8x12
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

    -- Verification of xor function (Registers not included)
    d_8x12(0) <= xor_reduce(di(5 downto 0) & di(5+48 downto 0+48));
    d_8x12(1) <= xor_reduce(di(5+6 downto 0+6) & di(5+48+6 downto 0+48+6));
    d_8x12(2) <= xor_reduce(di(5+12 downto 0+12) & di(5+48+12 downto 0+48+12));
    d_8x12(3) <= xor_reduce(di(5+18 downto 0+18) & di(5+48+18 downto 0+48+18));
    d_8x12(4) <= xor_reduce(di(5+24 downto 0+24) & di(5+48+24 downto 0+48+24));
    d_8x12(5) <= xor_reduce(di(5+30 downto 0+30) & di(5+48+30 downto 0+48+30));
    d_8x12(6) <= xor_reduce(di(5+36 downto 0+36) & di(5+48+36 downto 0+48+36));
    d_8x12(7) <= xor_reduce(di(5+42 downto 0+42) & di(5+48+42 downto 0+48+42));

    -- Simulating input flow
    input_flow : process
    begin

        -- Initialize input interface
        di    <= X"000000000000000000000000";
        cei   <= '1';
        ceo   <= '1';

        wait for RESET_TIME;
        wait for 10*CLKPER;

        for i in 0 to 95 loop
            di    <= (others => '0');
            di(I) <= '1';
            wait for CLKPER;

            report "DO_8x12: " & integer'image(conv_integer(do_8x12)) &
                   " Bit position: " & integer'image(I);
        end loop;

        wait;

    end process;

end architecture;
