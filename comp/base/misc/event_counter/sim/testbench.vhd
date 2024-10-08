-- testbench.vhd.
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use std.env.all;
use STD.textio.all;

library work;
use work.type_pack.all;
use work.math_pack.all;
use work.basics_test_pkg.all;
use std.env.stop;
use STD.textio.all;

entity TESTBENCH is
end entity TESTBENCH;

architecture BEHAVIORAL of TESTBENCH is

    constant CLK_PERIOD   : time := 1 ns;
    constant EVENT_VLD_CH : natural := 30;

    constant MAX_INTERVAL_CYCLES   : natural := 2**12-1;
    constant MAX_CONCURRENT_EVENTS : natural := 8;

    constant MI_WIDTH              : natural := 32;
    constant MI_INTERVAL_ADDR      : std_logic_vector(MI_WIDTH-1 downto 0) := (0 => '0', others => '0');
    constant MI_EVENTS_ADDR        : std_logic_vector(MI_WIDTH-1 downto 0) := (9 => '1', 0 => '1', others => '0');
    constant MI_ADDR_MASK          : std_logic_vector(MI_WIDTH-1 downto 0) := (0 => '1', others => '0');

    signal CLK       : std_logic;
    signal RESET     : std_logic;

    signal MI_DWR    : std_logic_vector(MI_WIDTH-1 downto 0);
    signal MI_ADDR   : std_logic_vector(MI_WIDTH-1 downto 0);
    signal MI_RD     : std_logic;
    signal MI_WR     : std_logic;
    signal MI_ARDY   : std_logic;
    signal MI_DRD    : std_logic_vector(MI_WIDTH-1 downto 0);
    signal MI_DRDY   : std_logic;

    signal EVENT_CNT : std_logic_vector(log2(MAX_CONCURRENT_EVENTS+1)-1 downto 0);
    signal EVENT_VLD : std_logic;

begin

    uut : entity work.EVENT_COUNTER_MI_WRAPPER
    generic map(
        MAX_INTERVAL_CYCLES   => MAX_INTERVAL_CYCLES  ,
        MAX_CONCURRENT_EVENTS => MAX_CONCURRENT_EVENTS,
        MI_WIDTH              => MI_WIDTH             ,
        MI_INTERVAL_ADDR      => MI_INTERVAL_ADDR     ,
        MI_EVENTS_ADDR        => MI_EVENTS_ADDR       ,
        MI_ADDR_MASK          => MI_ADDR_MASK
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        MI_DWR  => MI_DWR ,
        MI_ADDR => MI_ADDR,
        MI_RD   => MI_RD  ,
        MI_WR   => MI_WR  ,
        MI_ARDY => MI_ARDY,
        MI_DRD  => MI_DRD ,
        MI_DRDY => MI_DRDY,

        EVENT_CNT => EVENT_CNT,
        EVENT_VLD => EVENT_VLD
    );

    -- generating clock signal
    clk_pr : process
    begin
        CLK <= '1';
        wait for CLK_PERIOD/2;
        CLK <= '0';
        wait for CLK_PERIOD/2;
    end process;

    -- generating reset signal
    reset_pr : process
    begin
        RESET <= '1';
        wait for CLK_PERIOD*2;
        RESET <= '0';
        wait;
    end process;

    -- Event input generation
    eve_input_pr : process
        variable s0 : integer := 11;
        variable s1 : integer := 15;
        variable X  : integer := 0;
    begin
        EVENT_VLD <= '0';

        wait for CLK_PERIOD/2;
        wait until RESET/='1';
        wait for CLK_PERIOD/2;

        while (true) loop
            randint(s0,s1,0,MAX_CONCURRENT_EVENTS,X);
            EVENT_CNT <= std_logic_vector(to_unsigned(X,EVENT_CNT'length));
            EVENT_VLD <= '0';

            randint(s0,s1,0,99,X);
            if (X<EVENT_VLD_CH) then
                EVENT_VLD <= '1';
            end if;
            wait for CLK_PERIOD;
        end loop;

        wait;
    end process;

    -- MI input generation
    mi_input_pr : process
        variable s0 : integer := 11;
        variable s1 : integer := 15;
        variable X  : integer := 0;
    begin
        MI_WR     <= '0';
        MI_RD     <= '0';

        wait for CLK_PERIOD/2;
        wait until RESET/='1';
        wait for CLK_PERIOD/2;

        wait for CLK_PERIOD*8;

        while (true) loop
            -- Generate random interval
            randint(s0,s1,1,20,X);
            -- Set interval
            MI_ADDR <= (5 => '1', others => '0');
            MI_DWR  <= std_logic_vector(to_unsigned(X,MI_WIDTH));
            MI_WR   <= '1';
            MI_RD   <= '0';

            wait for CLK_PERIOD;

            for i in 0 to 2*X+2-1 loop
                MI_DWR  <= std_logic_vector(to_unsigned(X+i,MI_WIDTH));

                -- Read interval
                MI_ADDR <= (1 => '1', 0 => '0', others => '0');
                MI_WR   <= '0';
                MI_RD   <= '1';

                wait for CLK_PERIOD;

                -- Read events count
                MI_ADDR <= (6 => '1', 0 => '1', others => '0');
                MI_WR   <= '0';
                MI_RD   <= '1';

                wait for CLK_PERIOD;
            end loop;

            MI_WR <= '0';
            MI_RD <= '1';
            wait for CLK_PERIOD*8;
        end loop;

        wait;
    end process;

end architecture;
