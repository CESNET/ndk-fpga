-- hbm_tester_adc.vhd:
-- Copyright (C) 2024 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity HBM_TESTER_ADC is
    generic(
        PORTS     : natural := 16;
        CNT_WIDTH : natural := 16  -- max = 32, min 8
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK              : in  std_logic;
        RESET            : in  std_logic;

        -- =====================================================================
        -- MI32 INTERFACE
        -- =====================================================================
        MI_DWR           : in  std_logic_vector(31 downto 0);
        MI_ADDR          : in  std_logic_vector(31 downto 0);
        MI_BE            : in  std_logic_vector(3 downto 0);
        MI_RD            : in  std_logic;
        MI_WR            : in  std_logic;
        MI_ARDY          : out std_logic;
        MI_DRD           : out std_logic_vector(31 downto 0);
        MI_DRDY          : out std_logic;

        -- =====================================================================
        -- DEBUG INTERFACE
        -- =====================================================================
        -- Mode of increment address: 0 = sequential, 1 = pseudorandom
        DB_GEN_ADDR_MODE : out std_logic;
        -- Generator conection control: 0 = USER <-> HBM, 1 = GEN <-> HBM
        DB_GEN_CONNECT   : out std_logic;
        DB_GEN_BL8_MODE  : out std_logic;
        -- Generator run mode: "11" = RD and WR,
        --                     "10" = only RD,
        --                     "01" = only WR,
        --                     "00" = no requests
        DB_GEN_RUN_MODE  : out std_logic_vector(1 downto 0);
        -- Generator control per pseudo-channel: 0 = stop, 1 = run
        DB_GEN_RUN       : out std_logic_vector(PORTS-1 downto 0);
        DB_GEN_RW_SWITCH : out std_logic;
        -- Generator dead data: 0 = counter value, 1 = dead cafe
        DB_GEN_WR_DEAD   : out std_logic;
        -- Time of monitoring in clock cycles
        DB_MON_TIME      : out std_logic_vector(CNT_WIDTH-1 downto 0);
        -- Monitoring is done (monitoring time is out) and statistics are ready,
        -- for next monitoring is need monitor reset
        DB_MON_DONE      : in  std_logic_vector(PORTS-1 downto 0);
        -- Monitor reset, this clean statistics counters
        DB_MON_RESET     : out std_logic_vector(PORTS-1 downto 0);
        -- Counters mode: 000 = monitoring of read data words
        --                001 = monitoring of write data words
        --                010 = monitoring of read latency
        --                011 = monitoring of write latency
        --                100 = monitoring of read data ok
        --                101 = monitoring of read data error
        DB_MON_CNT0_MODE : out std_logic_vector(3-1 downto 0);
        DB_MON_CNT1_MODE : out std_logic_vector(3-1 downto 0);
        -- Outputs of configurable counters
        DB_STAT_CNT0     : in  slv_array_t(PORTS-1 downto 0)(CNT_WIDTH-1 downto 0);
        DB_STAT_CNT1     : in  slv_array_t(PORTS-1 downto 0)(CNT_WIDTH-1 downto 0)
    );
end HBM_TESTER_ADC;

architecture FULL of HBM_TESTER_ADC is

    constant VERSION : std_logic_vector(31 downto 0) := X"20240119";

    signal s_reg_gen_run_sel     : std_logic;
    signal s_reg_config_sel      : std_logic;
    signal s_reg_mon_reset_sel   : std_logic;
    signal s_reg_mon_time_sel    : std_logic;
    signal s_reg_gen_run_we      : std_logic;
    signal s_reg_config_we       : std_logic;
    signal s_reg_mon_reset_we    : std_logic;
    signal s_reg_mon_time_we     : std_logic;

    signal s_dbg_reg_common      : std_logic_vector(32-1 downto 0);
    signal s_reg_stat_cnt0_muxed : std_logic_vector(32-1 downto 0);
    signal s_reg_stat_cnt1_muxed : std_logic_vector(32-1 downto 0);
    signal s_dbg_reg_per_pcc     : std_logic_vector(32-1 downto 0);
    signal s_mi_drd              : std_logic_vector(32-1 downto 0);

    signal s_reg_gen_run         : std_logic_vector(32-1 downto 0);
    signal s_reg_config          : std_logic_vector(32-1 downto 0);
    signal s_reg_mon_reset       : std_logic_vector(32-1 downto 0);
    signal s_reg_mon_time        : std_logic_vector(32-1 downto 0);
    signal s_reg_mon_done        : std_logic_vector(32-1 downto 0);
    signal s_reg_stat_cnt0       : slv_array_t(PORTS-1 downto 0)(32-1 downto 0);
    signal s_reg_stat_cnt1       : slv_array_t(PORTS-1 downto 0)(32-1 downto 0);

begin

    -- =========================================================================
    --  DEBUG ADDRESS DECODER
    -- =========================================================================

    MI_ARDY <= MI_RD or MI_WR;

    -- -------------------------------------------------------------------------
    --  MI32 WRITE CONTROL
    -- -------------------------------------------------------------------------

    s_reg_gen_run_sel   <= '1' when (MI_ADDR(11 downto 0) = X"010") else '0';
    s_reg_config_sel    <= '1' when (MI_ADDR(11 downto 0) = X"014") else '0';
    s_reg_mon_reset_sel <= '1' when (MI_ADDR(11 downto 0) = X"018") else '0';
    s_reg_mon_time_sel  <= '1' when (MI_ADDR(11 downto 0) = X"01C") else '0';

    s_reg_gen_run_we   <= MI_WR and s_reg_gen_run_sel;
    s_reg_config_we    <= MI_WR and s_reg_config_sel;
    s_reg_mon_reset_we <= MI_WR and s_reg_mon_reset_sel;
    s_reg_mon_time_we  <= MI_WR and s_reg_mon_time_sel;

    -- -------------------------------------------------------------------------
    --  MI32 READ CONTROL
    -- -------------------------------------------------------------------------

    dbg_reg_common_p : process(all)
    begin
        case (MI_ADDR(7 downto 0)) is
            when X"00" =>
                s_dbg_reg_common <= VERSION;
            when X"10" =>
                s_dbg_reg_common <= s_reg_gen_run;
            when X"14" =>
                s_dbg_reg_common <= s_reg_config;
            when X"18" =>
                s_dbg_reg_common <= s_reg_mon_reset;
            when X"1C" =>
                s_dbg_reg_common <= s_reg_mon_time;
            when X"20" =>
                s_dbg_reg_common <= s_reg_mon_done;
            when others =>
                s_dbg_reg_common <= X"DEADCAFE";
        end case;
    end process;

    s_reg_stat_cnt0_muxed <= s_reg_stat_cnt0(to_integer(unsigned(MI_ADDR(8 downto 4))));
    s_reg_stat_cnt1_muxed <= s_reg_stat_cnt1(to_integer(unsigned(MI_ADDR(8 downto 4))));

    dbg_reg_per_pcc_p : process(all)
    begin
        case (MI_ADDR(3 downto 0)) is
            when "0000" =>
                s_dbg_reg_per_pcc <= s_reg_stat_cnt0_muxed;
            when "0100" =>
                s_dbg_reg_per_pcc <= s_reg_stat_cnt1_muxed;
            when others =>
                s_dbg_reg_per_pcc <= X"DEADCAFE";
        end case;
    end process;

    mi_drd_p : process(all)
    begin
        case (MI_ADDR(11 downto 9)) is
            when "000" =>
                s_mi_drd <= s_dbg_reg_common;
            when "001" =>
                s_mi_drd <= s_dbg_reg_per_pcc;
            when others =>
                s_mi_drd <= X"DEADCAFE";
        end case;
    end process;

    mi_drd_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            MI_DRD <= s_mi_drd;
        end if;
    end process;

    mi_drdy_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                MI_DRDY <= '0';
            else
                MI_DRDY <= MI_RD;
            end if;
        end if;
    end process;

    -- =========================================================================
    --  DEBUG REGISTERS
    -- =========================================================================

    -- -------------------------------------------------------------------------
    --  GENERATOR RUN VECTOR REGISTER (RW)
    --  ADDR: 0x010
    -- -------------------------------------------------------------------------

    reg_gen_run_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg_gen_run <= (others => '0');
            elsif (s_reg_gen_run_we = '1') then
                s_reg_gen_run <= MI_DWR;
            end if;
        end if;
    end process;

    DB_GEN_RUN <= s_reg_gen_run(PORTS-1 downto 0);

    -- -------------------------------------------------------------------------
    --  CONFIGURATION REGISTER (RW)
    --  ADDR: 0x014
    -- -------------------------------------------------------------------------

    reg_config_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg_config <= (others => '0');
            elsif (s_reg_config_we = '1') then
                s_reg_config <= MI_DWR;
            end if;
        end if;
    end process;

    DB_MON_CNT1_MODE <= s_reg_config(14 downto 12);
    DB_MON_CNT0_MODE <= s_reg_config(10 downto 8);
    DB_GEN_BL8_MODE  <= s_reg_config(6);
    DB_GEN_RUN_MODE  <= s_reg_config(5 downto 4);
    DB_GEN_RW_SWITCH <= s_reg_config(3);
    DB_GEN_WR_DEAD   <= s_reg_config(2);
    DB_GEN_ADDR_MODE <= s_reg_config(1);
    DB_GEN_CONNECT   <= s_reg_config(0);

    -- -------------------------------------------------------------------------
    --  MONITOR RESET VECTOR REGISTER (RW)
    --  ADDR: 0x018
    -- -------------------------------------------------------------------------

    reg_mon_reset_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg_mon_reset <= (others => '0');
            elsif (s_reg_mon_reset_we = '1') then
                s_reg_mon_reset <= MI_DWR;
            end if;
        end if;
    end process;

    DB_MON_RESET <= s_reg_mon_reset(PORTS-1 downto 0);

    -- -------------------------------------------------------------------------
    --  MONITOR TIME COMMON REGISTER (RW)
    --  ADDR: 0x01C
    -- -------------------------------------------------------------------------

    reg_mon_time_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg_mon_time <= X"0000FFFF";
            elsif (s_reg_mon_time_we = '1') then
                s_reg_mon_time <= MI_DWR;
            end if;
        end if;
    end process;

    DB_MON_TIME <= s_reg_mon_time(CNT_WIDTH-1 downto 0);

    -- -------------------------------------------------------------------------
    --  MONITOR DONE VECTOR REGISTER (RO)
    --  ADDR: 0x020
    -- -------------------------------------------------------------------------

    reg_mon_done_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_reg_mon_done <= (others => '0');
            s_reg_mon_done(PORTS-1 downto 0) <= DB_MON_DONE;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  MONITOR COUNTER 0 REGISTERS PER HBM PSEUDO CHANNEL (RO)
    --  ADDR: 0x200 + Y0, Y=NUMBER_OF_PSEUDO_CHANNEL (COUNTED FROM ZERO)
    -- -------------------------------------------------------------------------

    reg_stat_cnt0_g : for i in 0 to PORTS-1 generate
        reg_stat_cnt0_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                s_reg_stat_cnt0(i) <= (others => '0');
                s_reg_stat_cnt0(i)(CNT_WIDTH-1 downto 0) <= DB_STAT_CNT0(i);
            end if;
        end process;
    end generate;

    -- -------------------------------------------------------------------------
    --  MONITOR COUNTER 1 REGISTERS PER HBM PSEUDO CHANNEL (RO)
    --  ADDR: 0x200 + Y4, Y=NUMBER_OF_PSEUDO_CHANNEL (COUNTED FROM ZERO)
    -- -------------------------------------------------------------------------

    reg_stat_cnt1_g : for i in 0 to PORTS-1 generate
        reg_stat_cnt1_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                s_reg_stat_cnt1(i) <= (others => '0');
                s_reg_stat_cnt1(i)(CNT_WIDTH-1 downto 0) <= DB_STAT_CNT1(i);
            end if;
        end process;
    end generate;

end architecture;
