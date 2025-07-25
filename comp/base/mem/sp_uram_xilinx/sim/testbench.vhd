
--
-- testbench.vhd: Testbench for SP_URAM_XILINX
-- Copyright (C) 2018 CESNET
-- Author(s): Kamil Vojanec <xvojan00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use ieee.numeric_std.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TESTBENCH is
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture SP_URAM_XILINX of TESTBENCH is
    signal clk     : std_logic := '1';
    signal rst     : std_logic := '0';
    signal pipe_en : std_logic := '1';
    signal reg_ce  : std_logic := '1';
    signal re      : std_logic := '0';
    signal we      : std_logic := '0';
    signal addr    : std_logic_vector(11 downto 0);
    signal di      : std_logic_vector(71 downto 0);
    signal do      : std_logic_vector(71 downto 0);
    signal do_dv   : std_logic;
begin
    uut: entity work.SP_URAM_XILINX
    generic map (
        DEVICE                      => "ULTRASCALE",
        DATA_WIDTH                  => 72,
        ADDRESS_WIDTH               => 12,
        WRITE_MODE                  => "READ_FIRST",
        ADDITIONAL_REG              => 0,
        EXTERNAL_OUT_REG            => false,
        INTERNAL_OUT_REG            => false
    )
    port map (
        CLK         => clk,
        RST         => rst,
        PIPE_EN     => pipe_en,
        RE          => re,
        WE          => we,
        ADDR        => addr,
        DI          => di,
        DO          => do,
        DO_DV       => do_dv
    );

    clk <= not clk after 10 ns;

    test : process
    begin
        rst     <= '1';
        wait for 80 ns;
        rst     <= '0';
        pipe_en <= '1';
        wait for 80 ns;
        addr    <= std_logic_vector(to_unsigned(48,12));
        di      <= std_logic_vector(to_unsigned(121, 72));
        we      <= '1';
        re      <= '1';
        wait for 20 ns;
        we      <= '0';
        re      <= '0';
        wait for 20 ns;

        addr    <= std_logic_vector(to_unsigned(42, 12));
        di      <= std_logic_vector(to_unsigned(22,72));
        we      <= '1';
        wait for 20 ns;
        we      <= '0';
        re      <= '1';
        wait for 20 ns;
        re      <= '0';
        wait for 20 ns;
        re      <= '1';
        wait for 20 ns;
        re      <= '0';
        wait for 20 ns;
        addr    <= std_logic_vector(to_unsigned(99, 12));
        di      <= std_logic_vector(to_unsigned(44, 72));
        we      <= '1';
        wait for 20 ns;
        we      <= '0';
        re      <= '1';
        wait for 20 ns;
        re      <= '0';
        wait for 60 ns;
        addr    <= std_logic_vector(to_unsigned(77, 12));
        di      <= std_logic_vector(to_unsigned(66, 72));
        we      <= '1';
        wait for 20 ns;
        we      <= '0';
        re      <= '1';
        wait for 20 ns;
        re      <= '0';
        wait for 40 ns;
        addr    <= std_logic_vector(to_unsigned(48,12));
        di      <= std_logic_vector(to_unsigned(111, 72));
        we      <= '1';
        re      <= '1';
        wait for 20 ns;
        addr    <= std_logic_vector(to_unsigned(49,12));
        di      <= std_logic_vector(to_unsigned(121, 72));
        wait for 20 ns;
        addr    <= std_logic_vector(to_unsigned(50,12));
        di      <= std_logic_vector(to_unsigned(131, 72));
        wait for 20 ns;
        addr    <= std_logic_vector(to_unsigned(51,12));
        di      <= std_logic_vector(to_unsigned(231, 72));
        wait for 20 ns;
        pipe_en <= '0';
        we      <= '0';
        re      <= '0';
        wait for 20 ns;
        addr    <= std_logic_vector(to_unsigned(54,12));
        di      <= std_logic_vector(to_unsigned(261, 72));
        we      <= '1';
        re      <= '1';
        wait for 20 ns;
        we      <= '0';
        re      <= '0';
        wait for 60 ns;
        pipe_en <= '1';
        wait;
    end process;


end architecture;

