-- testbench.vhd.
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use std.env.all;
use std.textio.all;

library work;
use work.type_pack.all;
use work.math_pack.all;
use work.basics_test_pkg.all;
use std.env.stop;
use std.textio.all;

entity TESTBENCH is
end entity;

architecture BEHAVIORAL of TESTBENCH is

    constant CLK_PERIOD   : time := 1 ns;
    constant EVENT_VLD_CH : natural := 30;

    constant MAX_INTERVAL_CYCLES   : natural := 2**12-1;
    constant MAX_CONCURRENT_EVENTS : natural := 8;

    constant MI_WIDTH              : natural := 32;
    constant MI_INTERVAL_ADDR      : std_logic_vector(MI_WIDTH-1 downto 0) := (0 => '0', others => '0');
    constant MI_EVENTS_ADDR        : std_logic_vector(MI_WIDTH-1 downto 0) := (9 => '1', 0 => '1', others => '0');
    constant MI_ADDR_MASK          : std_logic_vector(MI_WIDTH-1 downto 0) := (0 => '1', others => '0');

    signal clk       : std_logic;
    signal reset     : std_logic;

    signal mi_dwr    : std_logic_vector(MI_WIDTH-1 downto 0);
    signal mi_addr   : std_logic_vector(MI_WIDTH-1 downto 0);
    signal mi_rd     : std_logic;
    signal mi_wr     : std_logic;
    signal mi_ardy   : std_logic;
    signal mi_drd    : std_logic_vector(MI_WIDTH-1 downto 0);
    signal mi_drdy   : std_logic;

    signal event_cnt : std_logic_vector(log2(MAX_CONCURRENT_EVENTS+1)-1 downto 0);
    signal event_vld : std_logic;

begin

    uut : entity work.EVENT_COUNTER_MI_WRAPPER
    generic map (
        MAX_INTERVAL_CYCLES   => MAX_INTERVAL_CYCLES,
        MAX_CONCURRENT_EVENTS => MAX_CONCURRENT_EVENTS,
        MI_WIDTH              => MI_WIDTH,
        MI_INTERVAL_ADDR      => MI_INTERVAL_ADDR,
        MI_EVENTS_ADDR        => MI_EVENTS_ADDR,
        MI_ADDR_MASK          => MI_ADDR_MASK
    )
    port map (
        CLK   => clk,
        RESET => reset,

        MI_DWR  => mi_dwr,
        MI_ADDR => mi_addr,
        MI_RD   => mi_rd,
        MI_WR   => mi_wr,
        MI_ARDY => mi_ardy,
        MI_DRD  => mi_drd,
        MI_DRDY => mi_drdy,

        EVENT_CNT => event_cnt,
        EVENT_VLD => event_vld
    );

    -- generating clock signal
    clk_pr : process
    begin
        clk <= '1';
        wait for CLK_PERIOD/2;
        clk <= '0';
        wait for CLK_PERIOD/2;
    end process;

    -- generating reset signal
    reset_pr : process
    begin
        reset <= '1';
        wait for CLK_PERIOD*2;
        reset <= '0';
        wait;
    end process;

    -- Event input generation
    eve_input_pr : process
        variable s0 : integer := 11;
        variable s1 : integer := 15;
        variable x  : integer := 0;
    begin
        event_vld <= '0';

        wait for CLK_PERIOD/2;
        wait until reset /= '1';
        wait for CLK_PERIOD/2;

        while (true) loop
            randint(s0,s1,0,MAX_CONCURRENT_EVENTS,x);
            event_cnt <= std_logic_vector(to_unsigned(x,event_cnt'length));
            event_vld <= '0';

            randint(s0,s1,0,99,x);
            if (x < EVENT_VLD_CH) then
                event_vld <= '1';
            end if;
            wait for CLK_PERIOD;
        end loop;

        wait;
    end process;

    -- MI input generation
    mi_input_pr : process
        variable s0 : integer := 11;
        variable s1 : integer := 15;
        variable x  : integer := 0;
    begin
        mi_wr     <= '0';
        mi_rd     <= '0';

        wait for CLK_PERIOD/2;
        wait until reset /= '1';
        wait for CLK_PERIOD/2;

        wait for CLK_PERIOD*8;

        while (true) loop
            -- Generate random interval
            randint(s0,s1,1,20,x);
            -- Set interval
            mi_addr <= (5 => '1', others => '0');
            mi_dwr  <= std_logic_vector(to_unsigned(x,MI_WIDTH));
            mi_wr   <= '1';
            mi_rd   <= '0';

            wait for CLK_PERIOD;

            for i in 0 to 2*x+2-1 loop
                mi_dwr  <= std_logic_vector(to_unsigned(x+i,MI_WIDTH));

                -- Read interval
                mi_addr <= (1 => '1', 0 => '0', others => '0');
                mi_wr   <= '0';
                mi_rd   <= '1';

                wait for CLK_PERIOD;

                -- Read events count
                mi_addr <= (6 => '1', 0 => '1', others => '0');
                mi_wr   <= '0';
                mi_rd   <= '1';

                wait for CLK_PERIOD;
            end loop;

            mi_wr <= '0';
            mi_rd <= '1';
            wait for CLK_PERIOD*8;
        end loop;

        wait;
    end process;

end architecture;
