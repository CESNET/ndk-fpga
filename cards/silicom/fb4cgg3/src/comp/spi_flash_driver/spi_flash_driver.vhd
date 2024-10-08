-- spi_flash_driver.vhd: SPI FLASH driver for FB4CGG3 card
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity SPI_FLASH_DRIVER is
    port(
        CLK         : in  std_logic;
        RESET       : in  std_logic;

        REG_WR_EN   : in  std_logic;
        REG_WR_DATA : in  std_logic_vector(64-1 downto 0);
        REG_RD_DATA : out std_logic_vector(64-1 downto 0);

        SPI_CLK     : out std_logic;
        SPI_CS_N    : out std_logic;
        SPI_MOSI    : out std_logic;
        SPI_MISO    : in  std_logic
    );
end entity;

architecture FULL of SPI_FLASH_DRIVER is

    constant WORD_SIZE     : natural := 16;
    constant WR_STOP_DELAY : natural := 10;
    constant WR_WORDS      : natural := 3;
    constant RD_CLK_TIME   : natural := 2;

    type spi_fsm_t is (st_idle, st_write, st_write_period, st_wait, st_read,
        st_read_sample, st_read_wait0, st_read_wait1,
        st_read_period, st_read_done);

    signal ready              : std_logic;
    signal spi_wr_data        : std_logic_vector(WR_WORDS*WORD_SIZE-1 downto 0);
    signal spi_en             : std_logic;
    signal spi_rd_en          : std_logic;
    signal rd_start_delay_reg : unsigned(12-1 downto 0);

    signal spi_fsm_pst        : spi_fsm_t;
    signal spi_fsm_nst        : spi_fsm_t;
    signal mosi_reg           : std_logic_vector(WR_WORDS*WORD_SIZE-1 downto 0);
    signal mosi_reg_next      : std_logic_vector(WR_WORDS*WORD_SIZE-1 downto 0);
    signal miso_reg           : std_logic_vector(WORD_SIZE-1 downto 0);
    signal miso_reg_next      : std_logic_vector(WORD_SIZE-1 downto 0);
    signal wait_cnt_reg       : unsigned(12-1 downto 0);
    signal wait_cnt_next      : unsigned(12-1 downto 0);
    signal wr_cnt_reg         : unsigned(log2(WR_WORDS)-1 downto 0);
    signal wr_cnt_next        : unsigned(log2(WR_WORDS)-1 downto 0);
    signal rd_cnt_reg         : unsigned(log2(RD_CLK_TIME)-1 downto 0);
    signal rd_cnt_next        : unsigned(log2(RD_CLK_TIME)-1 downto 0);
    signal spi_done           : std_logic;
    signal spi_rd_data        : std_logic_vector(WORD_SIZE-1 downto 0);
    
    signal spi_clk_reg        : std_logic;
    signal spi_cs_n_reg       : std_logic;
    signal spi_mosi_reg       : std_logic;
    signal spi_clk_next       : std_logic;
    signal spi_cs_n_next      : std_logic;
    signal spi_mosi_next      : std_logic;

begin
 
    process(CLK)
    begin
        if rising_edge(CLK) then
            spi_en    <= '0';
            spi_rd_en <= '1'; -- TBD: disable read cycle for write command only
            if (REG_WR_EN = '1' and ready = '1') then
                spi_wr_data <= REG_WR_DATA(63 downto 32) & REG_WR_DATA(15 downto 0);
                spi_en      <= '1';
                if REG_WR_DATA(59) = '0' then
                    rd_start_delay_reg <= X"046";
                else -- second part of flash need more time before read
                    rd_start_delay_reg <= X"800";
                end if;
            end if; 
        end if;
    end process;

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (REG_WR_EN = '1' and ready = '1') then
                ready <= '0';
            end if;
            if (RESET = '1' or spi_done = '1') then
                spi_rd_data <= miso_reg_next;
                ready <= '1';
            end if;
        end if;
    end process;

    REG_RD_DATA(15 downto 0)  <= spi_rd_data;
    REG_RD_DATA(16)           <= ready;
    REG_RD_DATA(63 downto 17) <= (others => '0');

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            spi_fsm_pst  <= spi_fsm_nst;
            mosi_reg     <= mosi_reg_next;
            miso_reg     <= miso_reg_next;
            wait_cnt_reg <= wait_cnt_next;
            wr_cnt_reg   <= wr_cnt_next;
            rd_cnt_reg   <= rd_cnt_next;
            spi_clk_reg  <= spi_clk_next;
            spi_cs_n_reg <= spi_cs_n_next;
            spi_mosi_reg <= spi_mosi_next;
            if (RESET = '1') then
                spi_fsm_pst  <= st_idle;
                wait_cnt_reg <= (others => '0');
                wr_cnt_reg   <= (others => '0');
                rd_cnt_reg   <= (others => '0');
                spi_clk_reg  <= '1';
                spi_cs_n_reg <= '1';
                spi_mosi_reg <= '1';
            end if;
        end if;
    end process;
    
    process (all)
    begin
        spi_fsm_nst   <= spi_fsm_pst;
        mosi_reg_next <= mosi_reg;
        miso_reg_next <= miso_reg;
        wait_cnt_next <= wait_cnt_reg;
        wr_cnt_next   <= wr_cnt_reg;
        rd_cnt_next   <= rd_cnt_reg;
        spi_clk_next  <= spi_clk_reg;
        spi_cs_n_next <= spi_cs_n_reg;
        spi_mosi_next <= spi_mosi_reg;
        spi_done      <= '0';

        case (spi_fsm_pst) is
            when st_idle =>
                spi_clk_next  <= '1';
                spi_cs_n_next <= '1';
                spi_mosi_next <= '1';
                if (spi_en = '1') then
                    spi_fsm_nst   <= st_write;
                    mosi_reg_next <= spi_wr_data;
                    spi_cs_n_next <= '0';
                end if;

            when st_write =>
                spi_clk_next  <= '0';
                spi_mosi_next <= mosi_reg(mosi_reg'high);
                mosi_reg_next <= mosi_reg(mosi_reg'high-1 downto 0) & '0';
                spi_fsm_nst   <= st_write_period;

            when st_write_period =>
                spi_clk_next <= '1';
                if (wait_cnt_reg = WORD_SIZE-1) then
                    wait_cnt_next <= (others => '0');
                    spi_fsm_nst   <= st_wait;
                else
                    wait_cnt_next <= wait_cnt_reg + 1;
                    spi_fsm_nst   <= st_write;
                end if;

            when st_wait =>
                spi_clk_next <= '1';
                if (wait_cnt_reg = WR_STOP_DELAY) then
                    wait_cnt_next <= (others => '0');
                    wr_cnt_next   <= wr_cnt_reg + 1;
                    if (wr_cnt_reg = WR_WORDS-1) then
                        if (spi_rd_en = '1') then
                            spi_fsm_nst <= st_read;
                        else
                            spi_done <= '1';
                            spi_fsm_nst <= st_idle;
                        end if;
                    else
                        spi_fsm_nst <= st_write;
                    end if;
                else
                    wait_cnt_next <= wait_cnt_reg + 1;
                end if;

            when st_read =>
                if (wait_cnt_reg = rd_start_delay_reg) then
                    wait_cnt_next <= (others => '0');
                    spi_fsm_nst   <= st_read_sample;
                else
                    wait_cnt_next <= wait_cnt_reg + 1;
                end if;

            when st_read_sample =>
                miso_reg_next <= miso_reg(miso_reg'high-1 downto 0) & SPI_MISO;
                spi_clk_next  <= '0';
                spi_mosi_next <= '0';
                spi_fsm_nst   <= st_read_wait0;

            when st_read_wait0 =>
                spi_clk_next <= '0';
                if (rd_cnt_reg = RD_CLK_TIME-1) then
                    rd_cnt_next <= (others => '0');
                    spi_fsm_nst <= st_read_wait1;
                else
                    rd_cnt_next <= rd_cnt_reg + 1;
                end if;

            when st_read_wait1 =>
                spi_clk_next <= '1';
                if (rd_cnt_reg = RD_CLK_TIME-1) then
                    rd_cnt_next <= (others => '0');
                    spi_fsm_nst <= st_read_period;
                else
                    rd_cnt_next <= rd_cnt_reg + 1;
                end if;

            when st_read_period =>
                spi_clk_next <= '1';
                if (wait_cnt_reg = WORD_SIZE-1) then
                    wait_cnt_next <= (others => '0');
                    spi_fsm_nst <= st_read_done;
                else
                    wait_cnt_next <= wait_cnt_reg + 1;
                    spi_fsm_nst <= st_read_sample;
                end if;
 
            when st_read_done =>
                miso_reg_next <= miso_reg(miso_reg'high-1 downto 0) & SPI_MISO;
                spi_done <= '1';
                spi_fsm_nst <= st_idle;

        end case;
    end process;

    SPI_CLK    <= spi_clk_reg;
    SPI_CS_N   <= spi_cs_n_reg;
    SPI_MOSI   <= spi_mosi_reg;

end architecture;
