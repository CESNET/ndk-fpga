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

    constant CLK_M_PERIOD : time := 20 ns;
    constant CLK_S_PERIOD : time := 10 ns;

    -- Master interface
    signal clk_m     : std_logic := '0';
    signal reset_m   : std_logic := '0';
    signal mi_m_dwr  : std_logic_vector(31 downto 0);
    signal mi_m_mwr  : std_logic_vector(1 downto 0);
    signal mi_m_addr : std_logic_vector(31 downto 0);
    signal mi_m_rd   : std_logic := '0';
    signal mi_m_wr   : std_logic := '0';
    signal mi_m_be   : std_logic_vector(3 downto 0);
    signal mi_m_drd  : std_logic_vector(31 downto 0);
    signal mi_m_ardy : std_logic;
    signal mi_m_drdy : std_logic;

    -- Slave interface
    signal clk_s     : std_logic := '0';
    signal reset_s   : std_logic := '0';
    signal mi_s_dwr  : std_logic_vector(31 downto 0);
    signal mi_s_mwr  : std_logic_vector(1 downto 0);
    signal mi_s_addr : std_logic_vector(31 downto 0);
    signal mi_s_rd   : std_logic;
    signal mi_s_wr   : std_logic;
    signal mi_s_be   : std_logic_vector(3 downto 0);
    signal mi_s_drd  : std_logic_vector(31 downto 0);
    signal mi_s_ardy : std_logic := '0';
    signal mi_s_drdy : std_logic := '0';

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
        CLK_M     => clk_m,
        RESET_M   => reset_m,
        MI_M_DWR  => mi_m_dwr,
        MI_M_MWR  => mi_m_mwr,
        MI_M_ADDR => mi_m_addr,
        MI_M_RD   => mi_m_rd,
        MI_M_WR   => mi_m_wr,
        MI_M_BE   => mi_m_be,
        MI_M_DRD  => mi_m_drd,
        MI_M_ARDY => mi_m_ardy,
        MI_M_DRDY => mi_m_drdy,

        CLK_S     => clk_s,
        RESET_S   => reset_s,
        MI_S_DWR  => mi_s_dwr,
        MI_S_MWR  => mi_s_mwr,
        MI_S_ADDR => mi_s_addr,
        MI_S_RD   => mi_s_rd,
        MI_S_WR   => mi_s_wr,
        MI_S_BE   => mi_s_be,
        MI_S_DRD  => mi_s_drd,
        MI_S_ARDY => mi_s_ardy,
        MI_S_DRDY => mi_s_drdy
    );

    clk_m <= not clk_m after CLK_M_PERIOD/2;
    clk_s <= not clk_s after CLK_S_PERIOD/2;

    -- stimulus process
    stim_p : process
    begin

        -- initial reset of mi_async component
        reset_m   <= '1', '0' after CLK_M_PERIOD*5;
        reset_s   <= '1', '0' after CLK_S_PERIOD*5;
        wait for CLK_M_PERIOD*5;

        -----------------------------------------------------
        -- only MASTER RESET test
        -----------------------------------------------------
        -- send some random read requests
        mi_m_be   <= "1111";
        mi_m_mwr  <= "11";
        mi_m_dwr  <= (30 downto 28 => "111", others => '0');
        mi_m_addr <= (2 downto 0 => "111", others => '0');
        mi_m_rd   <= '1';
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_dwr  <= (29 downto 27 => "111", others => '0');
        mi_m_addr <= (3 downto 2 => "11", others => '0');
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_dwr  <= (28 downto 26 => "111", others => '0');
        mi_m_addr <= (4 downto 3 => "11", others => '0');
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_rd   <= '0';
        reset_m   <= '1';
        wait for CLK_M_PERIOD*2;
        reset_m   <= '0';

        -- here p_state = MASTER_RESET, MI_ASYNC is not receiving new requests and master is waiting on MI_M_ARDY
        -- process requests by slave (ignore answers by master after RESET_M)
        mi_s_ardy <= '1';
        wait until rising_edge(clk_s) and mi_s_rd = '1';
        wait until rising_edge(clk_s) and mi_s_rd = '1';
        wait until rising_edge(clk_s) and mi_s_rd = '1';
        mi_s_ardy <= '0';
        wait for CLK_S_PERIOD*5;
        mi_s_drd  <= (others => '1');
        mi_s_drdy <= '1';
        wait for CLK_S_PERIOD;
        mi_s_drd  <= (15 downto 0 => '1', others => '0');
        wait for CLK_S_PERIOD;
        mi_s_drd  <= (31 downto 16 => '1', others => '0');
        wait for CLK_S_PERIOD;
        mi_s_drdy <= '0';

        -----------------------------------------------------
        -- MASTER RESET, SLAVE RESET with delay test
        -----------------------------------------------------
        -- send some random read requests
        mi_m_dwr  <= (30 downto 28 => "111", others => '0');
        mi_m_addr <= (2 downto 0 => "111", others => '0');
        mi_m_rd   <= '1';
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_dwr  <= (29 downto 27 => "111", others => '0');
        mi_m_addr <= (3 downto 2 => "11", others => '0');
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_dwr  <= (28 downto 26 => "111", others => '0');
        mi_m_addr <= (4 downto 3 => "11", others => '0');
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_rd   <= '0';
        reset_m   <= '1';
        wait for CLK_M_PERIOD*2;
        reset_m   <= '0';

        -- process one request, then reset slave
        mi_s_ardy <= '1';
        wait until rising_edge(clk_s) and mi_s_rd = '1';
        mi_s_ardy <= '0';
        wait for CLK_S_PERIOD*2;
        mi_s_drd  <= (others => '1');
        mi_s_drdy <= '1';
        wait for CLK_S_PERIOD;
        mi_s_drdy <= '0';
        reset_s   <= '1';
        wait for CLK_S_PERIOD*5;
        reset_s   <= '0';

        -----------------------------------------------------
        -- only SLAVE RESET test
        -----------------------------------------------------
        -- send some random read requests
        mi_m_dwr  <= (30 downto 28 => "111", others => '0');
        mi_m_addr <= (2 downto 0 => "111", others => '0');
        mi_m_rd   <= '1';
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_dwr  <= (29 downto 27 => "111", others => '0');
        mi_m_addr <= (3 downto 2 => "11", others => '0');
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_dwr  <= (28 downto 26 => "111", others => '0');
        mi_m_addr <= (4 downto 3 => "11", others => '0');
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_rd   <= '0';

        -- slave reset (sending data, so that master doesn't get stuck)
        -- MI_M_DRDY active for number of cycles specified in drdy_status
        reset_s   <= '1';
        wait for CLK_S_PERIOD*5;
        reset_s   <= '0';

        -----------------------------------------------------
        -- SLAVE RESET, MASTER RESET with delay test
        -----------------------------------------------------
        -- send some random read requests
        mi_m_dwr  <= (30 downto 28 => "111", others => '0');
        mi_m_addr <= (2 downto 0 => "111", others => '0');
        mi_m_rd   <= '1';
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_dwr  <= (29 downto 27 => "111", others => '0');
        mi_m_addr <= (3 downto 2 => "11", others => '0');
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_dwr  <= (28 downto 26 => "111", others => '0');
        mi_m_addr <= (4 downto 3 => "11", others => '0');
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_rd   <= '0';

        -- slave reset, master reset with delay
        reset_s   <= '1', '0' after CLK_S_PERIOD*5;
        wait for CLK_S_PERIOD*2;
        reset_m   <= '1', '0' after CLK_M_PERIOD*5;

        -----------------------------------------------------
        -- SLAVE RESET and MASTER RESET in the same cycle test
        -----------------------------------------------------
        -- send some random read requests
        mi_m_dwr  <= (30 downto 28 => "111", others => '0');
        mi_m_addr <= (2 downto 0 => "111", others => '0');
        mi_m_rd   <= '1';
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_dwr  <= (29 downto 27 => "111", others => '0');
        mi_m_addr <= (3 downto 2 => "11", others => '0');
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_dwr  <= (28 downto 26 => "111", others => '0');
        mi_m_addr <= (4 downto 3 => "11", others => '0');
        wait until rising_edge(clk_m) and mi_m_ardy = '1';
        mi_m_rd   <= '0';

        -- comp reset
        reset_s   <= '1', '0' after CLK_S_PERIOD*5;
        reset_m   <= '1', '0' after CLK_M_PERIOD*5;

        wait;

    end process;

end architecture;
