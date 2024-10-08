-- testbench.vhd: Testbench for simulation of amm_mux component
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

    constant MUX_WIDTH                  : integer := 2;
    constant AMM_DATA_WIDTH             : integer := 8;
    constant AMM_ADDR_WIDTH             : integer := 2;
    constant AMM_BURST_COUNT_WIDTH      : integer := 2;

    constant AMM_CLK_PERIOD             : time := 4 ns;     -- 266.66 MHz
    constant AMM_RST_INIT_TIME          : time := 40 ns;

    signal sim_done                     : std_logic := '0';
    signal mux_sel                      : std_logic_vector(log2(MUX_WIDTH) - 1 downto 0);

    signal amm_clk                      : std_logic;
    signal amm_rst                      : std_logic;

    signal master_amm_ready             : std_logic;
    signal master_amm_read              : std_logic;
    signal master_amm_write             : std_logic;
    signal master_amm_read_data_valid   : std_logic;
    signal master_amm_address           : std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
    signal master_amm_read_data         : std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    signal master_amm_write_data        : std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    signal master_amm_burst_count       : std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);

    signal slave_amm_ready              : std_logic_vector(MUX_WIDTH - 1 downto 0);
    signal slave_amm_read               : std_logic_vector(MUX_WIDTH - 1 downto 0);
    signal slave_amm_write              : std_logic_vector(MUX_WIDTH - 1 downto 0);
    signal slave_amm_read_data_valid    : std_logic_vector(MUX_WIDTH - 1 downto 0);
    signal slave_amm_address            : slv_array_t(MUX_WIDTH - 1 downto 0)(AMM_ADDR_WIDTH - 1 downto 0);
    signal slave_amm_read_data          : slv_array_t(MUX_WIDTH - 1 downto 0)(AMM_DATA_WIDTH - 1 downto 0);
    signal slave_amm_write_data         : slv_array_t(MUX_WIDTH - 1 downto 0)(AMM_DATA_WIDTH - 1 downto 0);
    signal slave_amm_burst_count        : slv_array_t(MUX_WIDTH - 1 downto 0)(AMM_BURST_COUNT_WIDTH - 1 downto 0);

begin

    ---------
    -- UUT --
    ---------

    uut : entity work.AMM_MUX
    generic map (
        MUX_WIDTH               => 2,
        MUX_LATENCY             => 1,
        SLAVE_INPUT_REG         => true,
        MASTER_OUTPUT_REG       => true,
        MASTER_INPUT_LATENCY    => 3,

        AMM_DATA_WIDTH          => AMM_DATA_WIDTH,
        AMM_ADDR_WIDTH          => AMM_ADDR_WIDTH,
        AMM_BURST_COUNT_WIDTH   => AMM_BURST_COUNT_WIDTH
    )
    port map (
        AMM_CLK                     => amm_clk                   ,
        AMM_RST                     => amm_rst                   ,
        MUX_SEL                     => mux_sel                   ,

        MASTER_AMM_READY            => master_amm_ready          ,
        MASTER_AMM_READ             => master_amm_read           ,
        MASTER_AMM_WRITE            => master_amm_write          ,
        MASTER_AMM_READ_DATA_VALID  => master_amm_read_data_valid,
        MASTER_AMM_ADDRESS          => master_amm_address        ,
        MASTER_AMM_READ_DATA        => master_amm_read_data      ,
        MASTER_AMM_WRITE_DATA       => master_amm_write_data     ,
        MASTER_AMM_BURST_COUNT      => master_amm_burst_count    ,

        SLAVE_AMM_READY             => slave_amm_ready           ,
        SLAVE_AMM_READ              => slave_amm_read            ,
        SLAVE_AMM_WRITE             => slave_amm_write           ,
        SLAVE_AMM_READ_DATA_VALID   => slave_amm_read_data_valid ,
        SLAVE_AMM_ADDRESS           => slave_amm_address         ,
        SLAVE_AMM_READ_DATA         => slave_amm_read_data       ,
        SLAVE_AMM_WRITE_DATA        => slave_amm_write_data      ,
        SLAVE_AMM_BURST_COUNT       => slave_amm_burst_count
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

    main_p : process
    begin
        sim_done    <= '0';

        mux_sel                     <= std_logic_vector(to_unsigned(0, mux_sel'length));
        master_amm_ready            <= '0';
        master_amm_read_data_valid  <= '0';
        master_amm_read_data        <= std_logic_vector(to_unsigned(0, master_amm_read_data'length));

        slave_amm_read          (0) <= '0';
        slave_amm_write         (0) <= '0';
        slave_amm_address       (0) <= std_logic_vector(to_unsigned(0, slave_amm_address(0)'length));
        slave_amm_write_data    (0) <= std_logic_vector(to_unsigned(0, slave_amm_write_data(0)'length));
        slave_amm_burst_count   (0) <= std_logic_vector(to_unsigned(1, slave_amm_burst_count(0)'length));

        slave_amm_read          (1) <= '0';
        slave_amm_write         (1) <= '0';
        slave_amm_address       (1) <= std_logic_vector(to_unsigned(0, slave_amm_address(0)'length));
        slave_amm_write_data    (1) <= std_logic_vector(to_unsigned(0, slave_amm_write_data(0)'length));
        slave_amm_burst_count   (1) <= std_logic_vector(to_unsigned(1, slave_amm_burst_count(0)'length));

        wait until amm_rst = '0';
        wait for AMM_CLK_PERIOD * 10;

        mux_sel                     <= std_logic_vector(to_unsigned(1, mux_sel'length));
        master_amm_ready            <= '1';
        master_amm_read_data_valid  <= '1';
        master_amm_read_data        <= std_logic_vector(to_unsigned(7, master_amm_read_data'length));

        slave_amm_read          (0) <= '0';
        slave_amm_write         (0) <= '1';
        slave_amm_address       (0) <= std_logic_vector(to_unsigned(3, slave_amm_address(0)'length));
        slave_amm_write_data    (0) <= std_logic_vector(to_unsigned(5, slave_amm_write_data(0)'length));
        slave_amm_burst_count   (0) <= std_logic_vector(to_unsigned(2, slave_amm_burst_count(0)'length));

        slave_amm_read          (1) <= '1';
        slave_amm_write         (1) <= '0';
        slave_amm_address       (1) <= std_logic_vector(to_unsigned(6, slave_amm_address(0)'length));
        slave_amm_write_data    (1) <= std_logic_vector(to_unsigned(7, slave_amm_write_data(0)'length));
        slave_amm_burst_count   (1) <= std_logic_vector(to_unsigned(3, slave_amm_burst_count(0)'length));

        wait for AMM_CLK_PERIOD * 10;
        mux_sel                     <= std_logic_vector(to_unsigned(0, mux_sel'length));
        wait for AMM_CLK_PERIOD * 10;

        sim_done    <= '1';
        wait;
    end process;

end architecture;
