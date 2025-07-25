
--
-- testbench.vhd:
-- Copyright (C) 2004 CESNET
-- Author(s): Pecenka Tomas <pecenka@liberouter.org>
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
architecture SDP_URAM_XILINX of TESTBENCH is
    signal clk     : std_logic := '1';
    signal rstb    : std_logic := '0';
    signal pipe_en : std_logic := '1';
    signal reb     : std_logic := '0';
    signal wea     : std_logic := '0';
    signal addra   : std_logic_vector(11 downto 0);
    signal addrb   : std_logic_vector(11 downto 0);
    signal dia     : std_logic_vector(71 downto 0);
    signal dob     : std_logic_vector(71 downto 0);
    signal dob_dv  : std_logic;
begin
    uut: entity work.SDP_URAM_XILINX
    generic map (
        DEVICE                        => "BEHAVIORAL",
        WRITE_MODE                    => "WRITE_FIRST",
        DATA_WIDTH                    => 72,
        ADDRESS_WIDTH                 => 12,
        ADDITIONAL_REG                => 0,
        EXTERNAL_OUT_REG              => false,
        INTERNAL_OUT_REG              => false
    )
    port map (
        CLK            => clk,
        RSTB           => rstb,
        PIPE_EN        => pipe_en,
        REB            => reb,
        WEA            => wea,
        ADDRA          => addra,
        ADDRB          => addrb,
        DIA            => dia,
        DOB            => dob,
        DOB_DV         => dob_dv
    );

    clk <= not clk after 10 ns;

    test : process
    begin
        rstb    <= '1';
        wait for 80 ns;
        rstb    <= '0';
        pipe_en <= '1';
        wait for 80 ns;
        addra   <= std_logic_vector(to_unsigned(48,12));
        addrb   <= std_logic_vector(to_unsigned(48,12));
        dia     <= std_logic_vector(to_unsigned(121, 72));
        wea     <= '1';
        reb     <= '1';
        wait for 20 ns;
        wea     <= '0';
        reb     <= '0';
        wait for 20 ns;

        addra   <= std_logic_vector(to_unsigned(42, 12));
        dia     <= std_logic_vector(to_unsigned(22,72));
        wea     <= '1';
        wait for 20 ns;
        addrb   <= std_logic_vector(to_unsigned(42, 12));
        wea     <= '0';
        reb     <= '1';
        wait for 20 ns;
        reb     <= '0';
        wait for 20 ns;
        reb     <= '1';
        wait for 20 ns;
        reb     <= '0';
        wait for 20 ns;
        addra   <= std_logic_vector(to_unsigned(99, 12));
        dia     <= std_logic_vector(to_unsigned(44, 72));
        wea     <= '1';
        wait for 20 ns;
        addrb   <= std_logic_vector(to_unsigned(99, 12));
        wea     <= '0';
        reb     <= '1';
        wait for 20 ns;
        reb     <= '0';
        wait for 60 ns;
        addra   <= std_logic_vector(to_unsigned(77, 12));
        dia     <= std_logic_vector(to_unsigned(66, 72));
        wea     <= '1';
        wait for 20 ns;
        addrb   <= std_logic_vector(to_unsigned(77, 12));
        wea     <= '0';
        reb     <= '1';
        wait for 20 ns;
        reb     <= '0';
        wait for 40 ns;
        addra   <= std_logic_vector(to_unsigned(48,12));
        addrb   <= std_logic_vector(to_unsigned(48,12));
        dia     <= std_logic_vector(to_unsigned(111, 72));
        wea     <= '1';
        reb     <= '1';
        wait for 20 ns;
        addra   <= std_logic_vector(to_unsigned(49,12));
        addrb   <= std_logic_vector(to_unsigned(49,12));
        dia     <= std_logic_vector(to_unsigned(121, 72));
        wait for 20 ns;
        addra   <= std_logic_vector(to_unsigned(50,12));
        dia     <= std_logic_vector(to_unsigned(131, 72));
        wait for 20 ns;
        addra   <= std_logic_vector(to_unsigned(51,12));
        addrb   <= std_logic_vector(to_unsigned(51,12));
        dia     <= std_logic_vector(to_unsigned(231, 72));
        wait for 20 ns;
        pipe_en <= '0';
        wea     <= '0';
        reb     <= '0';
        wait for 60 ns;
        pipe_en <= '1';
        wait;
    end process;


end architecture;
