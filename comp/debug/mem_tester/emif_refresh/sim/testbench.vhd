-- testbench.vhd: Testbench for simulation of emif_referesh component
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


entity TESTBENCH is
end entity;

architecture BEHAVIORAL Of TESTBENCH is
    constant DEVICE                 : string := "STRATIX10";
    constant RANK_CNT               : integer := 4;

    constant AMM_DATA_WIDTH         : integer := 32;
    constant AMM_ADDR_WIDTH         : integer := 10;
    constant AMM_BURST_COUNT_WIDTH  : integer := 2;

    constant REFRESH_PERIOD_WIDTH   : integer := 10;
    constant REFRESH_PERIOD_TICKS   : std_logic_vector(REFRESH_PERIOD_WIDTH - 1 downto 0)
        := std_logic_vector(to_unsigned(100, REFRESH_PERIOD_WIDTH));

    constant AMM_CLK_PERIOD         : time := 4 ns;     -- 266.66 MHz
    constant AMM_RST_INIT_TIME      : time := 40 ns;

    signal amm_clk                  : std_logic;
    signal amm_rst                  : std_logic;

    signal sim_done                 : std_logic := '0';
    signal refresh                  : std_logic_vector(RANK_CNT - 1 downto 0);

    -- Avalon interface
    signal amm_ready                : std_logic                      := '0';
    signal amm_read                 : std_logic                      := '0';
    signal amm_write                : std_logic                      := '0';
    signal amm_address              : std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0)  := (others => '0');
    signal amm_read_data            : std_logic_vector(AMM_DATA_WIDTH - 1 downto 0) := (others => '0');
    signal amm_write_data           : std_logic_vector(AMM_DATA_WIDTH - 1 downto 0) := (others => '0');
    signal amm_burst_count          : std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0)   := (others => '0');
    signal amm_read_data_valid      : std_logic                      := '0';

begin

    ---------
    -- UUT --
    ---------

    uut : entity work.EMIF_REFRESH
    generic map (
        AMM_DATA_WIDTH          => AMM_DATA_WIDTH,
        AMM_ADDR_WIDTH          => AMM_ADDR_WIDTH,
        AMM_BURST_COUNT_WIDTH   => AMM_BURST_COUNT_WIDTH,

        PERIODIC_REFRESH        => true,
        REFRESH_PERIOD_WIDTH    => REFRESH_PERIOD_WIDTH,

        RANK_CNT                => RANK_CNT,
        REFRESH_REG_ADDR        => 44,
        DEVICE                  => DEVICE
    )
    port map (
        CLK                     => amm_clk,
        RST                     => amm_rst,

        REFRESH                 => refresh,
        REFRESH_PERIOD_TICKS    => REFRESH_PERIOD_TICKS,

        AMM_READY               => amm_ready,
        AMM_READ                => amm_read,
        AMM_WRITE               => amm_write,
        AMM_ADDRESS             => amm_address,
        AMM_READ_DATA           => amm_read_data,
        AMM_WRITE_DATA          => amm_write_data,
        AMM_BURST_COUNT         => amm_burst_count,
        AMM_READ_DATA_VALID     => amm_read_data_valid
    );

    -- clock generators
    amm_clk_gen_p : process
    begin
        if (sim_done = '1') then
            wait;
        end if;

        amm_clk <= '1';
        wait for AMM_CLK_PERIOD / 2;
        amm_clk <= '0';
        wait for AMM_CLK_PERIOD / 2;
    end process;

    -- reset generators
    amm_reset_gen_p : process
    begin
        if (sim_done = '1') then
            wait;
        end if;

        amm_rst <= '1';
        wait for AMM_RST_INIT_TIME;
        amm_rst <= '0';
        wait;
    end process;

    resp_p : process
    begin
        if (sim_done = '1') then
            wait;
        end if;

        if (amm_read = '1') then
            wait for AMM_CLK_PERIOD * 5;

            amm_read_data(0)    <= '0';
            amm_read_data_valid <= '1';
            wait for AMM_CLK_PERIOD * 1;
            amm_read_data(0)    <= '1';
            amm_read_data_valid <= '0';
        end if;
        wait for AMM_CLK_PERIOD * 1;
    end process;

    main_p : process
    begin
        sim_done    <= '0';
        refresh     <= (others => '0');
        wait until amm_rst = '0';

        refresh     <= (others => '1');
        wait for AMM_CLK_PERIOD * 10;
        amm_ready   <= '1';
        wait for AMM_CLK_PERIOD * 10;
        amm_ready   <= '0';
        refresh     <= (others => '0');
        wait for AMM_CLK_PERIOD * 10;

        refresh     <= (others => '1');
        amm_ready   <= '1';
        wait for AMM_CLK_PERIOD * 10;
        refresh     <= (others => '0');

        wait for AMM_CLK_PERIOD * 200;

        sim_done    <= '1';
        wait;
    end process;

end architecture;
