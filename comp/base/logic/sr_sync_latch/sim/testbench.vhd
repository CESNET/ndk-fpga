-- testbench.vhd: SR synchronous latch testbench
-- Copyright (c) 2021 CESNET z.s.p.o.
-- Author: Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;

-------------------------------------------------------------------------------

entity TESTBENCH is

end entity;

-------------------------------------------------------------------------------

architecture BEHAVIORAL of TESTBENCH is

    -- component generics
    constant DATA_WIDTH : positive := 4;

    -- component ports
    signal clk       : std_logic;
    signal set       : std_logic;
    signal reset     : std_logic;
    signal data_in   : std_logic_vector((DATA_WIDTH - 1) downto 0);
    signal latch_out : std_logic_vector((DATA_WIDTH - 1) downto 0);

    constant clk_period : time := 2640 ps;
begin  -- architecture BEHAVIORAL

    -- component instantiation
    uut_i: entity work.SR_SYNC_LATCH
        generic map (
            DATA_WIDTH => DATA_WIDTH)
        port map (
            CLK       => clk,
            SET       => set,
            RESET     => reset,
            LATCH_OUT => latch_out);

-- clock generation
    clk_p: process
    begin
        clk <= '0';
        wait for clk_period/2;
        clk <= '1';
        wait for clk_period/2;
    end process;

    -- waveform generation
    stim_p: process
    begin
        -- insert signal assignments here
        reset <= '1';
        wait for 1 US;
        reset <= '0';
        set <= '0';

        wait for 10*clk_period;

        data_in <= "1001";
        wait for 10*clk_period;

        set <= '1';
        wait for clk_period;
        set <= '0';

        wait for 1 US;

        -- data change should make zero change in output
        data_in <= "1100";

        wait for 1 US;
        set <= '1';
        wait for clk_period;
        set <= '0';

        wait for 1 US;

        reset <= '1';
        wait for clk_period;
        reset <= '0';

        wait;
    end process;



end architecture;
-------------------------------------------------------------------------------
