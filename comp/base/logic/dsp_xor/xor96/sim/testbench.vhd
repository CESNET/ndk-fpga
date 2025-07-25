-- testbench.vhd: Testbench for xor96
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
    signal do_96      : std_logic;                        -- Data output for 96-bit xor
    signal do_2x48    : std_logic_vector(1 downto 0);     -- Data output for 2x48-bit xor
    signal do_4x24    : std_logic_vector(3 downto 0);     -- Data output for 4x24-bit xor
    signal cei        : std_logic;                        -- Clock enable for input registers
    signal ceo        : std_logic;                        -- Clock enable for output registers

    -- Signals for verification of xor function
    signal d_96       : std_logic;                        -- Data output for 96-bit xor
    signal d_2x48     : std_logic_vector(1 downto 0);     -- Data output for 2x48-bit xor
    signal d_4x24     : std_logic_vector(3 downto 0);     -- Data output for 4x24-bit xor

begin
    -- xor96 entity
    uut : entity work.XOR96(VU_DSP)
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
        DO_96       => do_96,
        DO_2x48     => do_2x48,
        DO_4x24     => do_4x24
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
    d_96      <= xor_reduce(di);
    d_2x48(0) <= xor_reduce(di(23 downto 0) & di(23+48 downto 48));
    d_2x48(1) <= xor_reduce(di(23+24 downto 0+24) & di(23+48+24 downto 48+24));
    d_4x24(0) <= xor_reduce(di(11 downto 0) & di(11+48 downto 48));
    d_4x24(1) <= xor_reduce(di(11+12 downto 0+12) & di(11+48+12 downto 48+12));
    d_4x24(2) <= xor_reduce(di(11+24 downto 0+24) & di(11+48+24 downto 48+24));
    d_4x24(3) <= xor_reduce(di(11+36 downto 0+36) & di(11+48+36 downto 48+36));

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

            report "Output 2x48: " & integer'image(conv_integer(do_2x48)) &
                   " Output 4x24: " & integer'image(conv_integer(do_4x24)) &
                   " Bit position: " & integer'image(I);
        end loop;

        wait;

    end process;

end architecture;
