-- testbench.vhd: testbench for PULSE_SHORT entity
-- Copyright (c) 2020 CESNET z.s.p.o.
-- Author : Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-------------------------------------------------------------------------------

entity TESTBENCH is
end entity;

-------------------------------------------------------------------------------

architecture BEHAVIORAL of TESTBENCH is

    -- component ports
    signal aclk      : std_logic;
    signal bclk      : std_logic;
    signal rst       : std_logic;
    signal trigger   : std_logic;
    signal pulse_out : std_logic;

    constant aclk_period : time := 2560 PS;
    constant bclk_period : time := 2559 PS;

begin  -- architecture BEHAVIORAL

    -- component instantiation
    uut_i : entity work.PULSE_SHORT
        generic map (
            DELAY_COUNT => 10,
            ASYNC_MASK  => "111")
        port map (
            ACLK      => aclk,
            BCLK      => bclk,
            RST       => rst,
            TRIGGER   => trigger,
            PULSE_OUT => pulse_out);

-- clock generation
    aclk_p : process
    begin
        aclk <= '0';
        wait for aclk_period/2;
        aclk <= '1';
        wait for aclk_period/2;
    end process;

    bclk_p : process
    begin
        bclk <= '0';
        wait for bclk_period/2;
        bclk <= '1';
        wait for bclk_period/2;
    end process;

    -- waveform generation
    stim_p : process
    begin
        -- insert signal assignments here
        rst     <= '1';
        trigger <= '0';
        wait for 100 NS;
        rst     <= '0';

        wait for aclk_period*5;
        trigger <= '1';
        wait for aclk_period*5;
        trigger <= '0';

        wait for aclk_period*50;
        trigger <= '1';
        wait for aclk_period*100;
        trigger <= '0';

        wait;
    end process;

end architecture;

-------------------------------------------------------------------------------
