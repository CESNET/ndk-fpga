-- testbench.vhd: Testbench for MI_ASYNC component
-- Copyright (C) 2022 CESNET z.s.p.o.
-- Author: Jakub Cabal <cabal@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity TESTBENCH is
end entity;

architecture FULL of TESTBENCH is

    constant CLK_PERIOD : time := 4 ns;
    constant WORD_SIZE  : natural := 16;
    constant TRANS_COUNT: natural := 16;
    

    signal clk         : std_logic := '0';
    signal reset       : std_logic;
    signal reg_wr_en   : std_logic;
    signal reg_wr_data : std_logic_vector(64-1 downto 0);
    signal reg_rd_data : std_logic_vector(64-1 downto 0);
    signal spi_clk     : std_logic;
    signal spi_cs_n    : std_logic;
    signal spi_mosi    : std_logic;
    signal spi_miso    : std_logic;

    signal slave_di : std_logic_vector(WORD_SIZE-1 downto 0);
    signal slave_do : std_logic_vector(WORD_SIZE-1 downto 0);

    procedure SPI_SLAVE (
        signal SSM_SDI  : in  std_logic_vector(WORD_SIZE-1 downto 0);
        signal SSM_SDO  : out std_logic_vector(WORD_SIZE-1 downto 0);
        signal SSM_SCLK : in  std_logic;
        signal SSM_CS_N : in  std_logic;
        signal SSM_MOSI : in  std_logic;
        signal SSM_MISO : out std_logic
    ) is
    begin
        --wait until SSM_CS_N = '0';
        for i in 0 to (WORD_SIZE-1) loop
            SSM_MISO <= SSM_SDI(WORD_SIZE-1-i);
            wait until rising_edge(SSM_SCLK);
            SSM_SDO(WORD_SIZE-1-i) <= SSM_MOSI;
            wait until falling_edge(SSM_SCLK);
        end loop;
    end procedure;

begin

    -- instantiate the unit under test (UUT)
    uut_i: entity work.SPI_FLASH_DRIVER
    port map (
        CLK         => clk,
        RESET       => reset,

        REG_WR_EN   => reg_wr_en,
        REG_WR_DATA => reg_wr_data,
        REG_RD_DATA => reg_rd_data,

        SPI_CLK     => spi_clk,
        SPI_CS_N    => spi_cs_n,
        SPI_MOSI    => spi_mosi,
        SPI_MISO    => spi_miso
    );

    clk <= not clk after CLK_PERIOD/2;

    stim_p : process
    begin
        reg_wr_en <= '0';
        -- initial reset
        reset <= '1', '0' after CLK_PERIOD*5;
        wait for CLK_PERIOD*5;

        -- send some requests
        reg_wr_data <= X"1000000000000000";
        reg_wr_en <= '1';
        wait until rising_edge(clk);
        reg_wr_en <= '0';
        wait until reg_rd_data(16) = '1';
        wait until rising_edge(clk);
        reg_wr_data <= X"2000000000000000";
        reg_wr_en <= '1';
        wait until rising_edge(clk);
        reg_wr_en <= '0';
        wait;

    end process;

    slave_model_p : process
    begin
        wait until reset = '0';
        for i in 0 to TRANS_COUNT-1 loop
            slave_di <= std_logic_vector(to_unsigned(i,WORD_SIZE));
            SPI_SLAVE(slave_di, slave_do, spi_clk, spi_cs_n, spi_mosi, spi_miso);
            report "Transactions received from master 1: " & to_hstring(slave_do) & "h";
        end loop;
        wait;
    end process;

end architecture;
