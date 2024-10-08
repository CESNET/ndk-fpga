-- testbench.vhd: Testbench for MI_INDIRECT_ACCESS component
-- Copyright (C) 2021 CESNET z.s.p.o.
-- Author: Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


entity TESTBENCH is
end entity;

architecture FULL of TESTBENCH is

    constant CLK_PERIOD : time := 10 ns;

    constant ADDR_WIDTH : natural := 32;
    constant DATA_WIDTH : natural := 32;

    constant OUTPUT_INTERFACES : natural := 3;

    -- =======================
    -- Addresses of registers
    -- =======================

    -- 0x00
    constant INF_REG_ADDR             : std_logic_vector(7 downto 2) := "000000";
    -- 0x04
    constant ADDR_REG_ADDR            : std_logic_vector(7 downto 2) := "000001";
    -- 0x08
    constant DWR_REG_ADDR             : std_logic_vector(7 downto 2) := "000010";
    -- 0x0C
    constant DRD_REG_ADDR             : std_logic_vector(7 downto 2) := "000011";
    -- 0x10
    constant COMMAND_REG_ADDR         : std_logic_vector(7 downto 2) := "000100";
    -- 0x14
    constant STATUS_REG_ADDR          : std_logic_vector(7 downto 2) := "000101";

    -- =======================
    -- Common interface
    -- =======================

    signal clk       : std_logic := '0';
    signal reset     : std_logic := '1';

    -- =======================
    -- Master interface
    -- =======================

    signal rx_mi_addr   : std_logic_vector(ADDR_WIDTH-1 downto 0);
    signal rx_mi_dwr    : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal rx_mi_wr     : std_logic := '0';
    signal rx_mi_rd     : std_logic := '0';
    signal rx_mi_drd    : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal rx_mi_ardy   : std_logic;
    signal rx_mi_drdy   : std_logic;

    -- =======================
    -- Slave interfaces
    -- =======================

    signal tx_mi_addr   : slv_array_t     (OUTPUT_INTERFACES-1 downto 0)(ADDR_WIDTH-1 downto 0);
    signal tx_mi_dwr    : slv_array_t     (OUTPUT_INTERFACES-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal tx_mi_wr     : std_logic_vector(OUTPUT_INTERFACES-1 downto 0);
    signal tx_mi_rd     : std_logic_vector(OUTPUT_INTERFACES-1 downto 0);
    signal tx_mi_drd    : slv_array_t     (OUTPUT_INTERFACES-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal tx_mi_ardy   : std_logic_vector(OUTPUT_INTERFACES-1 downto 0) := (others => '0');
    signal tx_mi_drdy   : std_logic_vector(OUTPUT_INTERFACES-1 downto 0) := (others => '0');

    -- =======================
    -- other signals
    -- =======================

    signal inf          : natural;
    signal verdict      : std_logic := '1';

begin

    uut_i: entity work.MI_INDIRECT_ACCESS
    generic map (
        DATA_WIDTH        => DATA_WIDTH,
        ADDR_WIDTH        => ADDR_WIDTH,
        OUTPUT_INTERFACES => OUTPUT_INTERFACES
    )
    port map (
        CLK   => clk  ,
        RESET => reset,

        RX_ADDR => rx_mi_addr,
        RX_DWR  => rx_mi_dwr ,
        RX_WR   => rx_mi_wr  ,
        RX_RD   => rx_mi_rd  ,
        RX_ARDY => rx_mi_ardy,
        RX_DRD  => rx_mi_drd ,
        RX_DRDY => rx_mi_drdy,

        TX_ADDR => tx_mi_addr,
        TX_DWR  => tx_mi_dwr ,
        TX_WR   => tx_mi_wr  ,
        TX_RD   => tx_mi_rd  ,
        TX_ARDY => tx_mi_ardy,
        TX_DRD  => tx_mi_drd ,
        TX_DRDY => tx_mi_drdy
    );

    CLK <= not CLK after CLK_PERIOD/2;

    stim_p : process
    begin

        -- initial reset
        reset <= '1', '0' after CLK_PERIOD*5;
        wait until reset = '0';

        -- ==================================================
        -- indirect WRITE request to INF 0
        -- ==================================================
        inf <= 0; -- could be generated randomly
        -- 1) set interface
        wait until rising_edge(CLK);
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => INF_REG_ADDR, others => '0');
        rx_mi_dwr  <= std_logic_vector(to_unsigned(inf, DATA_WIDTH)); -- (log2(OUTPUT_INTERFACES)-1 downto 0 => "00", others => '0');
        rx_mi_wr   <= '1';
        -- 2) set ADDR
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => ADDR_REG_ADDR, others => '0');
        rx_mi_dwr  <= (2-1 downto 0 => "11", others => '0');
        rx_mi_wr   <= '1';
        -- 3) set DWR
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => DWR_REG_ADDR, others => '0');
        rx_mi_dwr  <= (32-1 downto 29 => "111", others => '0');
        rx_mi_wr   <= '1';
        -- 4) set command to Write
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => COMMAND_REG_ADDR, others => '0');
        rx_mi_dwr  <= (1-1 downto 0 => '1', others => '0');
        rx_mi_wr   <= '1';

        wait for 1.16*CLK_PERIOD;
        rx_mi_wr   <= '0';

        -- read status (Busy bit)
        rx_mi_addr <= (7 downto 2 => STATUS_REG_ADDR, others => '0');
        rx_mi_rd   <= '1';
        wait until (rx_mi_drdy = '1') and (rx_mi_drd(0) = '0');
        wait for 0.16*CLK_PERIOD;
        rx_mi_rd   <= '0';

        -- ==================================================
        -- indirect WRITE request to INF 1
        -- ==================================================
        inf <= 1; -- could be generated randomly
        -- 1) set interface
        wait until rising_edge(CLK);
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => INF_REG_ADDR, others => '0');
        rx_mi_dwr  <= std_logic_vector(to_unsigned(inf, DATA_WIDTH));
        rx_mi_wr   <= '1';
        -- 2) set ADDR
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => ADDR_REG_ADDR, others => '0');
        rx_mi_dwr  <= (3-1 downto 0 => "100", others => '0');
        rx_mi_wr   <= '1';
        -- 3) set DWR
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => DWR_REG_ADDR, others => '0');
        rx_mi_dwr  <= (32-1 downto 29 => "110", others => '0');
        rx_mi_wr   <= '1';
        -- 4) set command to Write
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => COMMAND_REG_ADDR, others => '0');
        rx_mi_dwr  <= (1-1 downto 0 => '1', others => '0');
        rx_mi_wr   <= '1';

        wait for 1.16*CLK_PERIOD;
        rx_mi_wr   <= '0';

        -- read status (Busy bit)
        rx_mi_addr <= (7 downto 2 => STATUS_REG_ADDR, others => '0');
        rx_mi_rd   <= '1';
        wait until (rx_mi_drdy = '1') and (rx_mi_drd(0) = '0');
        wait for 0.16*CLK_PERIOD;
        rx_mi_rd   <= '0';

        -- ==================================================
        -- indirect WRITE request to INF 2
        -- ==================================================
        inf <= 2; -- could be generated randomly
        -- 1) set interface
        wait until rising_edge(CLK);
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => INF_REG_ADDR, others => '0');
        rx_mi_dwr  <= std_logic_vector(to_unsigned(inf, DATA_WIDTH));
        rx_mi_wr   <= '1';
        -- 2) set ADDR
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => ADDR_REG_ADDR, others => '0');
        rx_mi_dwr  <= (3-1 downto 0 => "101", others => '0');
        rx_mi_wr   <= '1';
        -- 3) set DWR
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => DWR_REG_ADDR, others => '0');
        rx_mi_dwr  <= (32-1 downto 29 => "101", others => '0');
        rx_mi_wr   <= '1';
        -- 4) set command to Write
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => COMMAND_REG_ADDR, others => '0');
        rx_mi_dwr  <= (1-1 downto 0 => '1', others => '0');
        rx_mi_wr   <= '1';

        wait for 1.16*CLK_PERIOD;
        rx_mi_wr   <= '0';

        -- read status (Busy bit)
        rx_mi_addr <= (7 downto 2 => STATUS_REG_ADDR, others => '0');
        rx_mi_rd   <= '1';
        wait until (rx_mi_drdy = '1') and (rx_mi_drd(0) = '0');
        wait for 0.16*CLK_PERIOD;
        rx_mi_rd   <= '0';

        -- --------------------------------------------------------------------------------------------------
        wait for 3*CLK_PERIOD;

        -- ==================================================
        -- indirect READ request to INF 0
        -- ==================================================
        inf <= 0; -- could be generated randomly
        -- 1) set interface
        wait until rising_edge(CLK);
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => INF_REG_ADDR, others => '0');
        rx_mi_dwr  <= std_logic_vector(to_unsigned(inf, DATA_WIDTH)); -- (log2(OUTPUT_INTERFACES)-1 downto 0 => "00", others => '0');
        rx_mi_wr   <= '1';
        -- 2) set ADDR
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => ADDR_REG_ADDR, others => '0');
        rx_mi_dwr  <= (2-1 downto 0 => "11", others => '0');
        rx_mi_wr   <= '1';
        -- 3) set command to Read
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => COMMAND_REG_ADDR, others => '0');
        rx_mi_dwr  <= (2-1 downto 1 => '1', others => '0');
        rx_mi_wr   <= '1';

        wait for 1.16*CLK_PERIOD;
        rx_mi_wr   <= '0';

        -- read status (Busy bit)
        rx_mi_addr <= (7 downto 2 => STATUS_REG_ADDR, others => '0');
        rx_mi_rd   <= '1';
        wait until (rx_mi_drdy = '1') and (rx_mi_drd(0) = '0');
        rx_mi_rd   <= '0';

        wait for 0.16*CLK_PERIOD;

        -- read DRD
        rx_mi_addr <= (7 downto 2 => DRD_REG_ADDR, others => '0');
        rx_mi_rd   <= '1';
        -- wait until (rx_mi_drdy = '1');
        -- verdict <= '1' when (unsigned(rx_mi_drd) = unsigned(tx_mi_drd(inf))) else '0';
        wait for 1.16*CLK_PERIOD;
        rx_mi_rd   <= '0';

        -- ==================================================
        -- indirect READ request to INF 1
        -- ==================================================
        inf <= 1; -- could be generated randomly
        -- 1) set interface
        wait until rising_edge(CLK);
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => INF_REG_ADDR, others => '0');
        rx_mi_dwr  <= std_logic_vector(to_unsigned(inf, DATA_WIDTH)); -- (log2(OUTPUT_INTERFACES)-1 downto 0 => "00", others => '0');
        rx_mi_wr   <= '1';
        -- 2) set ADDR
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => ADDR_REG_ADDR, others => '0');
        rx_mi_dwr  <= (2-1 downto 0 => "11", others => '0');
        rx_mi_wr   <= '1';
        -- 3) set command to Read
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => COMMAND_REG_ADDR, others => '0');
        rx_mi_dwr  <= (2-1 downto 1 => '1', others => '0');
        rx_mi_wr   <= '1';

        wait for 1.16*CLK_PERIOD;
        rx_mi_wr   <= '0';

        -- read status (Busy bit)
        rx_mi_addr <= (7 downto 2 => STATUS_REG_ADDR, others => '0');
        rx_mi_rd   <= '1';
        wait until (rx_mi_drdy = '1') and (rx_mi_drd(0) = '0');
        rx_mi_rd   <= '0';

        wait for 0.16*CLK_PERIOD;

        -- read DRD
        rx_mi_addr <= (7 downto 2 => DRD_REG_ADDR, others => '0');
        rx_mi_rd   <= '1';
        wait for 1.16*CLK_PERIOD;
        rx_mi_rd   <= '0';

        -- ==================================================
        -- indirect READ request to INF 2
        -- ==================================================
        inf <= 2; -- could be generated randomly
        -- 1) set interface
        wait until rising_edge(CLK);
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => INF_REG_ADDR, others => '0');
        rx_mi_dwr  <= std_logic_vector(to_unsigned(inf, DATA_WIDTH)); -- (log2(OUTPUT_INTERFACES)-1 downto 0 => "00", others => '0');
        rx_mi_wr   <= '1';
        -- 2) set ADDR
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => ADDR_REG_ADDR, others => '0');
        rx_mi_dwr  <= (2-1 downto 0 => "11", others => '0');
        rx_mi_wr   <= '1';
        -- 3) set command to Read
        wait until rising_edge(CLK) and rx_mi_ardy = '1';
        wait for 0.16*CLK_PERIOD;
        rx_mi_addr <= (7 downto 2 => COMMAND_REG_ADDR, others => '0');
        rx_mi_dwr  <= (2-1 downto 1 => '1', others => '0');
        rx_mi_wr   <= '1';

        wait for 1.16*CLK_PERIOD;
        rx_mi_wr   <= '0';

        -- read status (Busy bit)
        rx_mi_addr <= (7 downto 2 => STATUS_REG_ADDR, others => '0');
        rx_mi_rd   <= '1';
        wait until (rx_mi_drdy = '1') and (rx_mi_drd(0) = '0');
        rx_mi_rd   <= '0';

        wait for 0.16*CLK_PERIOD;

        -- read DRD
        rx_mi_addr <= (7 downto 2 => DRD_REG_ADDR, others => '0');
        rx_mi_rd   <= '1';
        wait for 1.16*CLK_PERIOD;
        rx_mi_rd   <= '0';

        wait;

    end process;

    ardy_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            tx_mi_ardy(0) <= tx_mi_wr(0) or tx_mi_rd(0);
            tx_mi_ardy(1) <= tx_mi_wr(1) or tx_mi_rd(1);
            tx_mi_ardy(2) <= tx_mi_wr(2) or tx_mi_rd(2);
        end if;
    end process;

    read_data_p : process
    begin

        tx_mi_drd (0) <= (28-1 downto 25 => "111", others => '0');
        wait until (tx_mi_rd(0) = '1') and (tx_mi_ardy(0) = '1');
        tx_mi_drdy(0) <= '1';
        wait for CLK_PERIOD;
        tx_mi_drdy(0) <= '0';
        tx_mi_drd (0) <= X"DEADCAFE";

        tx_mi_drd (1) <= (28-1 downto 25 => "110", others => '0');
        wait until tx_mi_rd(1) = '1' and (tx_mi_ardy(1) = '1');
        tx_mi_drdy(1) <= '1';
        wait for CLK_PERIOD;
        tx_mi_drdy(1) <= '0';
        tx_mi_drd (1) <= X"DEADCAFE";

        -- delayed DRDY
        tx_mi_drd (2) <= (28-1 downto 25 => "101", others => '0');
        wait until tx_mi_rd(2) = '1' and (tx_mi_ardy(2) = '1');
        wait for 2*CLK_PERIOD;
        tx_mi_drdy(2) <= '1';
        wait for 1*CLK_PERIOD;
        tx_mi_drdy(2) <= '0';
        tx_mi_drd (2) <= X"DEADCAFE";

        wait;

    end process;

end architecture;
