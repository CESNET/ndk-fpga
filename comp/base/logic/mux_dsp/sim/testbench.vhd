--! testbench.vhd: Testbench for MUX_DSP
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
use work.math_pack.all;

entity TESTBENCH is

end entity;

architecture BEHAVIORAL of TESTBENCH is

    constant CLKPER         : time := 10 ns;           -- Clock period
    constant RESET_TIME     : time := 2*CLKPER + 1 ns; -- Reset durati
    constant DATA_WIDTH     : integer := 8;
    constant MUX_WIDTH      : integer := 8;

    --! Clock and reset signals
    signal clk              : std_logic;
    signal reset            : std_logic;

    --! input and output
    signal data_in          : std_logic_vector(DATA_WIDTH*MUX_WIDTH-1 downto 0);
    signal ce_in            : std_logic;
    signal ce_lvl           : std_logic;
    signal sel              : std_logic_vector(log2(MUX_WIDTH)-1 downto 0);
    signal ce_out           : std_logic;
    signal data_out         : std_logic_vector(DATA_WIDTH-1 downto 0);

begin

    --! MUX_DSP
    uut : entity work.MUX_DSP_GEN
    generic map (
        DATA_WIDTH  => data_width,
        MUX_WIDTH   => mux_width,
        REG_IN      => 1,
        REG_OUT     => 0,
        REG_LVL     => 1
    )
    port map (
        CLK         => clk,
        RESET       => reset,
        DATA_IN     => data_in,
        CE_IN       => ce_in,
        CE_LVL      => ce_lvl,
        CE_OUT      => ce_out,
        SEL         => sel,
        DATA_OUT    => data_out
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
        ce_in    <= '1';
        ce_lvl   <= '1';
        ce_out   <= '1';
        data_in  <= X"0011223344556677";
        sel      <= "000";

        wait for RESET_TIME;
        wait for CLKPER;

        sel <= "001";
        wait for CLKPER;
        sel <= "010";
        wait;

    end process;
end architecture;
