-- hbm_tester_mon.vhd:
-- Copyright (C) 2024 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity HBM_TESTER_MON is
    generic(
        CNT_WIDTH : natural := 16
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK              : in  std_logic;
        RESET            : in  std_logic;
        -- =====================================================================
        -- CONTROL/STATUS INTERFACE
        -- =====================================================================
        -- Time of monitoring in clock cycles
        CS_MONITOR_TIME  : in  std_logic_vector(CNT_WIDTH-1 downto 0);
        -- Monitoring is done (monitoring time is out) and statistics are ready,
        -- for next monitoring is need monitor reset
        CS_MONITOR_DONE  : out std_logic;
        -- Monitor reset, this clean statistics counters
        CS_MONITOR_RESET : in  std_logic;
        -- Counters mode: 000 = monitoring of read data words
        --                001 = monitoring of write data words
        --                010 = monitoring of read latency
        --                011 = monitoring of write latency
        --                100 = monitoring of read data ok
        --                101 = monitoring of read data error
        CS_COUNTER0_MODE : in  std_logic_vector(3-1 downto 0);
        CS_COUNTER1_MODE : in  std_logic_vector(3-1 downto 0);
        -- Outputs of configurable counters
        CS_COUNTER0_OUT  : out std_logic_vector(CNT_WIDTH-1 downto 0);
        CS_COUNTER1_OUT  : out std_logic_vector(CNT_WIDTH-1 downto 0);
        -- =====================================================================
        -- MONITORED GENERATOR SIGNALS
        -- =====================================================================
        -- Increments of data checking, requires the correct sequence of tests
        GEN_DATA_OK_INC  : in std_logic;
        GEN_DATA_ERR_INC : in std_logic;
        -- =====================================================================
        -- MONITORED HBM SIMPLE INTERFACE (HSI)
        -- =====================================================================
        -- WRITE ADDR/DATA SIGNALS
        WR_VALID         : in  std_logic;
        WR_READY         : in  std_logic;
        -- WRITE RESPONSE SIGNALS
        WR_RSP_VALID     : in  std_logic;
        WR_RSP_READY     : in  std_logic;
        -- READ ADDRESS SIGNALS
        RD_ADDR_VALID    : in  std_logic;
        RD_ADDR_READY    : in  std_logic;
        -- READ DATA SIGNALS
        RD_DATA_VALID    : in  std_logic;
        RD_DATA_READY    : in  std_logic
    );
end HBM_TESTER_MON;

architecture FULL of HBM_TESTER_MON is

    signal s_wr_data_word         : std_logic;
    signal s_wr_resp_word         : std_logic;
    signal s_rd_addr_word         : std_logic;
    signal s_rd_data_word         : std_logic;
    signal s_gen_data_ok_inc_reg  : std_logic;
    signal s_gen_data_err_inc_reg : std_logic;

    signal s_monitor_start    : std_logic;
    signal s_monitor_busy     : std_logic;
    signal s_monitor_run_reg  : std_logic;
    signal s_monitor_run      : std_logic;
    signal s_monitor_time_cnt : unsigned(CNT_WIDTH-1 downto 0);
    signal s_monitor_done     : std_logic;

    signal s_wr_data_word_inc : std_logic;
    signal s_rd_data_word_inc : std_logic;
    signal s_rd_data_ok_inc   : std_logic;
    signal s_rd_data_err_inc  : std_logic;
    signal s_rd_latency_inc   : std_logic;
    signal s_wr_latency_inc   : std_logic;

    signal s_counter0_rst     : std_logic;
    signal s_counter0_max     : std_logic;
    signal s_counter0_en      : std_logic;
    signal s_counter0         : unsigned(CNT_WIDTH-1 downto 0);

    signal s_counter1_rst     : std_logic;
    signal s_counter1_max     : std_logic;
    signal s_counter1_en      : std_logic;
    signal s_counter1         : unsigned(CNT_WIDTH-1 downto 0);

begin

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_wr_data_word         <= WR_VALID and WR_READY;
            s_wr_resp_word         <= WR_RSP_VALID and WR_RSP_READY;
            s_rd_addr_word         <= RD_ADDR_VALID and RD_ADDR_READY;
            s_rd_data_word         <= RD_DATA_VALID and RD_DATA_READY;
            s_gen_data_ok_inc_reg  <= GEN_DATA_OK_INC;
            s_gen_data_err_inc_reg <= GEN_DATA_ERR_INC;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  MONITOR CONTROL
    -- -------------------------------------------------------------------------

    s_monitor_start <= s_wr_data_word or s_rd_addr_word;
    s_monitor_run   <= s_monitor_run_reg or (s_monitor_start and not s_monitor_busy);
    s_monitor_done  <= '1' when (s_monitor_time_cnt = unsigned(CS_MONITOR_TIME)) else '0';

    CS_MONITOR_DONE <= s_monitor_done;

    monitor_busy_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1' or CS_MONITOR_RESET = '1') then
                s_monitor_busy <= '0';
            elsif (s_monitor_start = '1') then
                s_monitor_busy <= '1';
            end if;
        end if;
    end process;

    monitor_run_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1' or s_monitor_done = '1') then
                s_monitor_run_reg <= '0';
            elsif (s_monitor_start = '1' and s_monitor_busy = '0') then
                s_monitor_run_reg <= '1';
            end if;
        end if;
    end process;

    monitor_time_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1' or CS_MONITOR_RESET = '1') then
                s_monitor_time_cnt <= (others => '0');
            elsif (s_monitor_run = '1') then
                if (s_monitor_done = '0') then
                    s_monitor_time_cnt <= s_monitor_time_cnt + 1;
                end if;
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  INCREMENTS FOR COUNTERS
    -- -------------------------------------------------------------------------

    s_wr_data_word_inc <= s_wr_data_word and s_monitor_run and not s_monitor_done;
    s_rd_data_word_inc <= s_rd_data_word and s_monitor_run and not s_monitor_done;

    s_rd_data_ok_inc  <= s_gen_data_ok_inc_reg and s_monitor_run and not s_monitor_done;
    s_rd_data_err_inc <= s_gen_data_err_inc_reg and s_monitor_run and not s_monitor_done;

    rd_latency_inc_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1' or s_rd_data_word = '1') then
                s_rd_latency_inc <= '0';
            elsif (s_rd_addr_word = '1' and s_monitor_busy = '0') then
                s_rd_latency_inc <= '1';
            end if;
        end if;
    end process;

    wr_latency_inc_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1' or s_wr_resp_word = '1') then
                s_wr_latency_inc <= '0';
            elsif (s_wr_data_word = '1' and s_monitor_busy = '0') then
                s_wr_latency_inc <= '1';
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  CONFIGURABLE COUNTER 0
    -- -------------------------------------------------------------------------

    s_counter0_rst <= RESET or CS_MONITOR_RESET;
    s_counter0_max <= s_counter0(CNT_WIDTH-1);

    with CS_COUNTER0_MODE select
    s_counter0_en <= s_rd_data_word_inc when "000", -- read data words monitoring
                     s_wr_data_word_inc when "001", -- write data words monitoring
                     s_rd_latency_inc   when "010", -- read latency monitoring
                     s_wr_latency_inc   when "011", -- write latency monitoring
                     s_rd_data_ok_inc   when "100", -- read data ok monitoring
                     s_rd_data_err_inc  when "101", -- read data error monitoring
                     '0'                when others;

    counter0_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_counter0_rst = '1') then
                s_counter0 <= (others => '0');
            elsif (s_counter0_en = '1' and s_counter0_max = '0') then
                s_counter0 <= s_counter0 + 1;
            end if;
        end if;
    end process;

    CS_COUNTER0_OUT <= std_logic_vector(s_counter0);

    -- -------------------------------------------------------------------------
    --  CONFIGURABLE COUNTER 1
    -- -------------------------------------------------------------------------

    s_counter1_rst <= RESET or CS_MONITOR_RESET;
    s_counter1_max <= s_counter1(CNT_WIDTH-1);

    with CS_COUNTER1_MODE select
    s_counter1_en <= s_rd_data_word_inc when "000", -- read data words monitoring
                     s_wr_data_word_inc when "001", -- write data words monitoring
                     s_rd_latency_inc   when "010", -- read latency monitoring
                     s_wr_latency_inc   when "011", -- write latency monitoring
                     s_rd_data_ok_inc   when "100", -- read data ok monitoring
                     s_rd_data_err_inc  when "101", -- read data error monitoring
                     '0'                when others;

    counter1_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_counter1_rst = '1') then
                s_counter1 <= (others => '0');
            elsif (s_counter1_en = '1' and s_counter1_max = '0') then
                s_counter1 <= s_counter1 + 1;
            end if;
        end if;
    end process;

    CS_COUNTER1_OUT <= std_logic_vector(s_counter1);

end architecture;
