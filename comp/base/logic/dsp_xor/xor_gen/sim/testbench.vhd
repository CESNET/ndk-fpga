-- testbench.vhd: Testbench for xor_gen
-- Copyright (C) 2018 CESNET
-- Author: Petr Panak <xpanak04@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_misc.all;

entity TESTBENCH is

end entity;

architecture BEHAVIORAL of TESTBENCH is

    constant CLKPER      : time := 10 ns;                 -- Clock period
    constant RESET_TIME  : time := 10*CLKPER + 1 ns;      -- Reset duration

    constant DATA_WIDTH  : integer := 384;                --! Data width (96, 192, 288, 384, 576, 768)

    -- Clock and reset signals
    signal clk           : std_logic;
    signal reset         : std_logic;

    -- Input and output
    signal di            : std_logic_vector(DATA_WIDTH-1 downto 0); -- Data input
    signal do_1          : std_logic;                               -- Data output
    signal do_2          : std_logic_vector(1 downto 0);            -- Data output
    signal do_4          : std_logic_vector(3 downto 0);            -- Data output
    signal cei           : std_logic;                               -- Clock enable for input registers
    signal ceo           : std_logic;                               -- Clock enable for output register

    -- Signal for verification of xor function
    signal d_1           : std_logic;

begin
    -- xor_gen
    uut : entity work.XOR_GEN
    generic map (
        DATA_WIDTH  => DATA_WIDTH,
        IREG        => 0,
        OREG        => 0
    )
    port map (
        CLK         => clk,
        RESET       => reset,

        DI          => di,
        DO_1        => do_1,
        DO_2        => do_2,
        DO_4        => do_4,
        CEI         => cei,
        CEO         => ceo
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

    -- Verification of xor function for DO_1 (Registers not included)
    d_1 <= xor_reduce(di(DATA_WIDTH-1 downto DATA_WIDTH/2) & di(DATA_WIDTH/2-1 downto 0));

    -- Simulating input flow
    input_flow : process
    begin

        -- Initialize input interface
        di <= (others => '0');                                                                                     -- output 0

        cei   <= '1';
        ceo   <= '1';

        wait for RESET_TIME;
        wait for 10*CLKPER;

        -- Data input only for 384-bit xor (Test of DO_1)
        di <= X"0000EFEFEBCAD0000000000000000000048998484810001561935240000ABEF00000000000FFFFFFFF00FF00000000FF"; -- output 1
        wait for CLKPER;

        di <= X"012345689ABC012345689ABC012345689ABC012345689ABC012345689ABC012345689ABC012345689ABC012345689ABC"; -- output 0
        wait for CLKPER;

        di <= X"264AB8695689153415BEF2A400000000000000000000000054681689300000ABB4598BCDE0000EDA00977413A0000000"; -- output 1
        wait for CLKPER;

        di <= X"ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111"; -- output 0
        wait for CLKPER;

        di <= X"000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"; -- output 0
        wait for CLKPER;

        di <= X"ABCD26891111ABCD26891111ABCD26891111ABCD26548613215984846516815549ABC6548613215984846516815549A1"; -- output 1
        wait for CLKPER;

        di <= X"264AB8695689153415BEF2A400000000000000000000000054681689300000ABB4598BCDE0000EDA00977413A0000000"; -- output 1
        wait for CLKPER;

        di <= X"ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111"; -- output 0
        wait for CLKPER;

        -- Data input for any DATA_WIDTH (Test of DO_2, DO_4)
        for i in 0 to DATA_WIDTH-1 loop
            di    <= (others => '0');
            di(I) <= '1';
            wait for CLKPER;

            report "DO_1: "  & integer'image(conv_integer(do_1)) &
                   " DO_2: " & integer'image(conv_integer(do_2(1))) &
                   integer'image(conv_integer(do_2(0))) &
                   " DO_4: " & integer'image(conv_integer(do_4(3))) &
                   integer'image(conv_integer(do_4(2)))&
                   integer'image(conv_integer(do_4(1)))&
                   integer'image(conv_integer(do_4(0)))&
                   " Bit position: " & integer'image(I);
        end loop;

        wait;

    end process;

end architecture;
