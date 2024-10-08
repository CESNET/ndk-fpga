-- event_counter.vhd: Event Counter Statistics unit
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- =========================================================================
--                                 Description
-- =========================================================================
-- Statistical unit for counting a number of occurences of a certain event
-- in a certain time interval.
-- =========================================================================

entity EVENT_COUNTER is
generic(
    -- Maximum number of CLK cycles in one counting interval
    -- Automatically rounded to the closes higher (2**N-1).
    MAX_INTERVAL_CYCLES     : natural := 2**12-1;
    -- Maximum number of event occurences in one CLK cycle
    -- Automatically rounded to the closes higher (2**N-1).
    MAX_CONCURRENT_EVENTS   : natural := 4
);
port(
    -- =====================================================================
    --  Clock and Reset
    -- =====================================================================

    CLK   : in  std_logic;
    RESET : in  std_logic;

    -- =====================================================================

    -- =====================================================================
    --  Other interfaces
    -- =====================================================================

    -- Configuration for a new counting interval
    INTERVAL_CYCLES : in  std_logic_vector(log2(MAX_INTERVAL_CYCLES+1)-1 downto 0);
    INTERVAL_SET    : in  std_logic;

    -- Event occurence propagation
    EVENT_CNT       : in  std_logic_vector(log2(MAX_CONCURRENT_EVENTS+1)-1 downto 0);
    EVENT_VLD       : in  std_logic;

    -- Total number of events during last whole interval
    -- The counter has such a width, that it cannot overflow during any possible interval.
    TOTAL_EVENTS    : out std_logic_vector(log2((MAX_INTERVAL_CYCLES+1)*(MAX_CONCURRENT_EVENTS+1))-1 downto 0);
    -- Total cycles passed during the last whole interval
    -- Should be the same value as the last valid INTERVAL_CYCLES
    TOTAL_CYCLES    : out std_logic_vector(log2(MAX_INTERVAL_CYCLES+1)-1 downto 0);
    -- Sets to '1' for one cycle each time TOTAL_EVENTS and TOTAL_CYCLES are updated
    TOTAL_UPDATE    : out std_logic

    -- =====================================================================
);
end entity;

architecture FULL of EVENT_COUNTER is

    signal int_cyc_reg     : unsigned(log2(MAX_INTERVAL_CYCLES+1)-1 downto 0);
    signal int_cyc_reg_vld : std_logic;
    signal eve_cnt_reg     : unsigned(log2((MAX_INTERVAL_CYCLES+1)*(MAX_CONCURRENT_EVENTS+1))-1 downto 0);
    signal int_pr_cnt_reg  : unsigned(log2(MAX_INTERVAL_CYCLES+1)-1 downto 0);
    signal int_reached     : std_logic;

begin

    -- =====================================================================
    --  Interval cycles register
    -- =====================================================================

    int_cyc_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (INTERVAL_SET='1') then
                int_cyc_reg     <= unsigned(INTERVAL_CYCLES);
                int_cyc_reg_vld <= '1';
            end if;

            if (RESET='1') then
                int_cyc_reg_vld <= '0';
            end if;
        end if;
    end process;

    -- =====================================================================

    -- =====================================================================
    --  Total events counter
    -- =====================================================================

    eve_cnt_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            -- Only increment when new events are valid
            if (EVENT_VLD='1') then
                eve_cnt_reg <= eve_cnt_reg + unsigned(EVENT_CNT);
            end if;

            -- Reset when end of interval has been reached OR new interval size is being set
            if (int_reached='1' or INTERVAL_SET='1') then
                eve_cnt_reg <= (others => '0');
            end if;

        end if;
    end process;

    -- =====================================================================

    -- =====================================================================
    --  Interval progress counter
    -- =====================================================================

    int_pr_cnt_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            -- Unset update flag
            TOTAL_UPDATE   <= '0';

            -- Increment number of passed cycles
            int_pr_cnt_reg <= int_pr_cnt_reg+1;

            -- Reset when end of interval has been reached
            if (int_reached='1') then
                int_pr_cnt_reg <= (others => '0');
                -- Propagate number of events and cycles counted
                TOTAL_EVENTS   <= std_logic_vector(eve_cnt_reg);
                TOTAL_CYCLES   <= std_logic_vector(int_pr_cnt_reg);
                TOTAL_UPDATE   <= '1';
            end if;

            -- Reset when new interval size is being set
            if (INTERVAL_SET='1') then
                int_pr_cnt_reg <= (others => '0');
            end if;

        end if;
    end process;

    int_reached <= '1' when int_pr_cnt_reg=int_cyc_reg and int_cyc_reg_vld='1' else '0';

    -- =====================================================================

end architecture;
