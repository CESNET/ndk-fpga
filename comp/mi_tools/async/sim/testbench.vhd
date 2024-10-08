-- testbench.vhd: Testbench for MI_ASYNC component
-- Copyright (C) 2020 CESNET z.s.p.o.
-- Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity TESTBENCH is
end entity;

architecture FULL of TESTBENCH is

    constant CLK_M_period : time := 20 ns;
    constant CLK_S_period : time := 10 ns;

    -- Master interface
    signal CLK_M     : std_logic := '0';
    signal RESET_M   : std_logic := '0';
    signal MI_M_DWR  : std_logic_vector(31 downto 0);
    signal MI_M_MWR  : std_logic_vector(1 downto 0);
    signal MI_M_ADDR : std_logic_vector(31 downto 0);
    signal MI_M_RD   : std_logic := '0';
    signal MI_M_WR   : std_logic := '0';
    signal MI_M_BE   : std_logic_vector(3 downto 0);
    signal MI_M_DRD  : std_logic_vector(31 downto 0);
    signal MI_M_ARDY : std_logic;
    signal MI_M_DRDY : std_logic;

     -- Slave interface
    signal CLK_S     : std_logic := '0';
    signal RESET_S   : std_logic := '0';
    signal MI_S_DWR  : std_logic_vector(31 downto 0);
    signal MI_S_MWR  : std_logic_vector(1 downto 0);
    signal MI_S_ADDR : std_logic_vector(31 downto 0);
    signal MI_S_RD   : std_logic;
    signal MI_S_WR   : std_logic;
    signal MI_S_BE   : std_logic_vector(3 downto 0);
    signal MI_S_DRD  : std_logic_vector(31 downto 0);
    signal MI_S_ARDY : std_logic := '0';
    signal MI_S_DRDY : std_logic := '0';

begin

    -- instantiate the unit under test (UUT)
    uut_i: entity work.MI_ASYNC
    generic map (
        DATA_WIDTH => 32,
        ADDR_WIDTH => 32,
        META_WIDTH => 2,
        RAM_TYPE   => "LUT",
        DEVICE     => "ULTRASCALE"
    )
    port map (
        CLK_M     => CLK_M    ,
        RESET_M   => RESET_M  ,
        MI_M_DWR  => MI_M_DWR ,
        MI_M_MWR  => MI_M_MWR ,
        MI_M_ADDR => MI_M_ADDR,
        MI_M_RD   => MI_M_RD  ,
        MI_M_WR   => MI_M_WR  ,
        MI_M_BE   => MI_M_BE  ,
        MI_M_DRD  => MI_M_DRD ,
        MI_M_ARDY => MI_M_ARDY,
        MI_M_DRDY => MI_M_DRDY,

        CLK_S     => CLK_S    ,
        RESET_S   => RESET_S  ,
        MI_S_DWR  => MI_S_DWR ,
        MI_S_MWR  => MI_S_MWR ,
        MI_S_ADDR => MI_S_ADDR,
        MI_S_RD   => MI_S_RD  ,
        MI_S_WR   => MI_S_WR  ,
        MI_S_BE   => MI_S_BE  ,
        MI_S_DRD  => MI_S_DRD ,
        MI_S_ARDY => MI_S_ARDY,
        MI_S_DRDY => MI_S_DRDY
    );

    CLK_M <= not CLK_M after CLK_M_period/2;
    CLK_S <= not CLK_S after CLK_S_period/2;

    -- stimulus process
    stim_p : process
    begin

        -- initial reset of mi_async component
        RESET_M   <= '1', '0' after CLK_M_period*5;
        RESET_S   <= '1', '0' after CLK_S_period*5;
        wait for CLK_M_period*5;

        -----------------------------------------------------
        -- only MASTER RESET test
        -----------------------------------------------------
        -- send some random read requests
        MI_M_BE   <= "1111";
        MI_M_MWR  <= "11";
        MI_M_DWR  <= (30 downto 28 => "111", others => '0');
        MI_M_ADDR <= (2 downto 0 => "111", others => '0');
        MI_M_RD   <= '1';
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_DWR  <= (29 downto 27 => "111", others => '0');
        MI_M_ADDR <= (3 downto 2 => "11", others => '0');
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_DWR  <= (28 downto 26 => "111", others => '0');
        MI_M_ADDR <= (4 downto 3 => "11", others => '0');
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_RD   <= '0';
        RESET_M   <= '1';
        wait for CLK_M_period*2;
        RESET_M   <= '0';

        -- here p_state = MASTER_RESET, MI_ASYNC is not receiving new requests and master is waiting on MI_M_ARDY
        -- process requests by slave (ignore answers by master after RESET_M)
        MI_S_ARDY <= '1';
        wait until rising_edge(CLK_S) and MI_S_RD = '1';
        wait until rising_edge(CLK_S) and MI_S_RD = '1';
        wait until rising_edge(CLK_S) and MI_S_RD = '1';
        MI_S_ARDY <= '0';
        wait for CLK_S_period*5;
        MI_S_DRD  <= (others => '1');
        MI_S_DRDY <= '1';
        wait for CLK_S_period;
        MI_S_DRD  <= (15 downto 0 => '1', others => '0');
        wait for CLK_S_period;
        MI_S_DRD  <= (31 downto 16 => '1', others => '0');
        wait for CLK_S_period;
        MI_S_DRDY <= '0';

        -----------------------------------------------------
        -- MASTER RESET, SLAVE RESET with delay test
        -----------------------------------------------------
        -- send some random read requests
        MI_M_DWR  <= (30 downto 28 => "111", others => '0');
        MI_M_ADDR <= (2 downto 0 => "111", others => '0');
        MI_M_RD   <= '1';
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_DWR  <= (29 downto 27 => "111", others => '0');
        MI_M_ADDR <= (3 downto 2 => "11", others => '0');
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_DWR  <= (28 downto 26 => "111", others => '0');
        MI_M_ADDR <= (4 downto 3 => "11", others => '0');
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_RD   <= '0';
        RESET_M   <= '1';
        wait for CLK_M_period*2;
        RESET_M   <= '0';

        -- process one request, then reset slave
        MI_S_ARDY <= '1';
        wait until rising_edge(CLK_S) and MI_S_RD = '1';
        MI_S_ARDY <= '0';
        wait for CLK_S_period*2;
        MI_S_DRD  <= (others => '1');
        MI_S_DRDY <= '1';
        wait for CLK_S_period;
        MI_S_DRDY <= '0';
        RESET_S   <= '1';
        wait for CLK_S_period*5;
        RESET_S   <= '0';

        -----------------------------------------------------
        -- only SLAVE RESET test
        -----------------------------------------------------
        -- send some random read requests
        MI_M_DWR  <= (30 downto 28 => "111", others => '0');
        MI_M_ADDR <= (2 downto 0 => "111", others => '0');
        MI_M_RD   <= '1';
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_DWR  <= (29 downto 27 => "111", others => '0');
        MI_M_ADDR <= (3 downto 2 => "11", others => '0');
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_DWR  <= (28 downto 26 => "111", others => '0');
        MI_M_ADDR <= (4 downto 3 => "11", others => '0');
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_RD   <= '0';

        -- slave reset (sending data, so that master doesn't get stuck)
        -- MI_M_DRDY active for number of cycles specified in drdy_status
        RESET_S   <= '1';
        wait for CLK_S_period*5;
        RESET_S   <= '0';

        -----------------------------------------------------
        -- SLAVE RESET, MASTER RESET with delay test
        -----------------------------------------------------
        -- send some random read requests
        MI_M_DWR  <= (30 downto 28 => "111", others => '0');
        MI_M_ADDR <= (2 downto 0 => "111", others => '0');
        MI_M_RD   <= '1';
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_DWR  <= (29 downto 27 => "111", others => '0');
        MI_M_ADDR <= (3 downto 2 => "11", others => '0');
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_DWR  <= (28 downto 26 => "111", others => '0');
        MI_M_ADDR <= (4 downto 3 => "11", others => '0');
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_RD   <= '0';

        -- slave reset, master reset with delay
        RESET_S   <= '1', '0' after CLK_S_period*5;
        wait for CLK_S_period*2;
        RESET_M   <= '1', '0' after CLK_M_period*5;

        -----------------------------------------------------
        -- SLAVE RESET and MASTER RESET in the same cycle test
        -----------------------------------------------------
        -- send some random read requests
        MI_M_DWR  <= (30 downto 28 => "111", others => '0');
        MI_M_ADDR <= (2 downto 0 => "111", others => '0');
        MI_M_RD   <= '1';
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_DWR  <= (29 downto 27 => "111", others => '0');
        MI_M_ADDR <= (3 downto 2 => "11", others => '0');
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_DWR  <= (28 downto 26 => "111", others => '0');
        MI_M_ADDR <= (4 downto 3 => "11", others => '0');
        wait until rising_edge(CLK_M) and MI_M_ARDY = '1';
        MI_M_RD   <= '0';

        -- comp reset
        RESET_S   <= '1', '0' after CLK_S_period*5;
        RESET_M   <= '1', '0' after CLK_M_period*5;

        wait;

    end process;

end architecture;
