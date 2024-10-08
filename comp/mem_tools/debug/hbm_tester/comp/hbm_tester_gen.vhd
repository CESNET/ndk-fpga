-- hbm_tester_gen.vhd:
-- Copyright (C) 2024 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity HBM_TESTER_GEN is
    generic(
        USR_DATA_WIDTH : natural := 256;
        AXI_ADDR_WIDTH : natural := 32;
        PORT_ADDR_HBIT : natural := AXI_ADDR_WIDTH;
        PORT_ID        : natural := 0
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK               : in  std_logic;
        RESET             : in  std_logic;

        -- =====================================================================
        -- CONTROL/STATUS INTERFACE
        -- =====================================================================
        -- Mode of increment address: 0 = sequential, 1 = pseudorandom
        CS_GEN_ADDR_MODE  : in  std_logic;
        CS_GEN_BL8_MODE   : in  std_logic;
        -- Generator run mode: "11" = RD and WR,
        --                     "10" = only RD,
        --                     "01" = only WR,
        --                     "00" = no requests
        CS_GEN_RUN_MODE   : in  std_logic_vector(1 downto 0);
        CS_GEN_RW_SWITCH  : in  std_logic;
        -- Generator dead data: 0 = counter value, 1 = dead cafe
        CS_GEN_WR_DEAD    : in  std_logic;
        -- Generator control: 0 = stop, 1 = run
        CS_GEN_RUN        : in  std_logic;

        -- =====================================================================
        -- STATISTICS INTERFACE
        -- =====================================================================
        -- Increments of data checking, requires the correct sequence of tests
        STAT_DATA_OK_INC  : out std_logic;
        STAT_DATA_ERR_INC : out std_logic;

        -- =====================================================================
        -- HBM SIMPLE INTERFACE (HSI)
        -- =====================================================================
        -- WRITE ADDR/DATA SIGNALS
        WR_ADDR           : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0) := (others => '0');
        WR_DATA           : out std_logic_vector(USR_DATA_WIDTH-1 downto 0);
        WR_DATA_LAST      : out std_logic;
        WR_VALID          : out std_logic;
        WR_READY          : in  std_logic;
        -- WRITE RESPONSE SIGNALS
        WR_RSP_ACK        : in  std_logic;
        WR_RSP_VALID      : in  std_logic;
        WR_RSP_READY      : out std_logic;
        -- READ ADDRESS SIGNALS
        RD_ADDR           : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0) := (others => '0');
        RD_ADDR_VALID     : out std_logic;
        RD_ADDR_READY     : in  std_logic;
        -- READ DATA SIGNALS
        RD_DATA           : in  std_logic_vector(USR_DATA_WIDTH-1 downto 0);
        RD_DATA_LAST      : in  std_logic;
        RD_DATA_VALID     : in  std_logic;
        RD_DATA_READY     : out std_logic
    );
end HBM_TESTER_GEN;

architecture FULL of HBM_TESTER_GEN is

    constant ADDR_GEN_WIDTH  : natural := PORT_ADDR_HBIT-5;
    constant PORT_ADDR_WIDTH : natural := AXI_ADDR_WIDTH-PORT_ADDR_HBIT;

    signal s_gen_run_reg       : std_logic;
    signal s_gen_run           : std_logic;
    signal s_gen_burst_cnt     : unsigned(1 downto 0);
    signal s_gen_burst_max     : unsigned(1 downto 0);
    signal s_gen_data_last     : std_logic;
    signal s_gen_rw_switch_en  : std_logic;
    signal s_gen_rw_switch     : std_logic;
    signal s_sequ_addr_inc     : unsigned(1 downto 0);
    signal s_sequ_wr_addr      : unsigned(ADDR_GEN_WIDTH-1 downto 0);
    signal s_sequ_wr_addr_en   : std_logic;
    signal s_sequ_rd_addr      : unsigned(ADDR_GEN_WIDTH-1 downto 0);
    signal s_sequ_rd_addr_en   : std_logic;
    signal s_rand_data         : std_logic_vector(ADDR_GEN_WIDTH+1-1 downto 0);
    signal s_rand_wr_addr      : std_logic_vector(ADDR_GEN_WIDTH-1 downto 0);
    signal s_rand_rd_addr      : std_logic_vector(ADDR_GEN_WIDTH-1 downto 0);
    signal s_write_data_vld    : std_logic;
    signal s_read_data_vld     : std_logic;
    signal s_data_ok           : std_logic;
    signal s_data_cnt_rst      : std_logic;
    signal s_data_cnt_en       : std_logic;
    signal s_data_cnt          : unsigned(7 downto 0);
    signal s_data_cnt2         : unsigned(7 downto 0);

begin

    s_gen_burst_max <= "01" when (CS_GEN_BL8_MODE = '1') else "00"; -- 64B access = 2 words, 32B access = 1 words
    s_sequ_addr_inc <= "10" when (CS_GEN_BL8_MODE = '1') else "01"; -- address + 2, address + 1

    -- -------------------------------------------------------------------------
    --  RUN CONTROL LOGIC
    -- -------------------------------------------------------------------------

    -- gen_run is high up to correctly end of transmitting
    s_gen_run <= (s_gen_run_reg and CS_GEN_RUN_MODE(0)) or CS_GEN_RUN;

    -- register enabling correctly end of transmitting (after last burst word)
    gen_run_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_gen_run_reg <= '0';
            elsif (CS_GEN_RUN = '1') then
                s_gen_run_reg <= '1';
            elsif (s_gen_data_last = '1' and WR_READY = '1') then
                s_gen_run_reg <= '0';
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  BURST CONTROL LOGIC
    -- -------------------------------------------------------------------------

    -- counter of word in burst
    gen_burst_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_gen_run = '1') then
                if (WR_READY = '1') then
                    if (s_gen_data_last = '1') then
                        s_gen_burst_cnt <= (others => '0');
                    else
                        s_gen_burst_cnt <= s_gen_burst_cnt + 1;
                    end if;
                end if;
            else
                s_gen_burst_cnt <= (others => '0');
            end if;
        end if;
    end process;

    -- flag of last burst word
    s_gen_data_last <= '1' when (s_gen_burst_cnt = s_gen_burst_max) else '0';


    s_gen_rw_switch_en <= (s_write_data_vld and s_gen_data_last) or (RD_ADDR_READY and RD_ADDR_VALID);

    gen_rw_switch_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_gen_run = '1') then
                if (s_gen_rw_switch_en = '1') then
                    s_gen_rw_switch <= not s_gen_rw_switch;
                end if;
            else
                s_gen_rw_switch <= '0';
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  PSEUDO-RANDOM ADDRESS GENERATOR
    -- -------------------------------------------------------------------------

    rand_i : entity work.LFSR_SIMPLE_RANDOM_GEN
    generic map(
        DATA_WIDTH => ADDR_GEN_WIDTH+1,
        RESET_SEED => std_logic_vector(to_unsigned(PORT_ID, ADDR_GEN_WIDTH+1))
    )
    port map(
        CLK    => CLK,
        RESET  => RESET,
        ENABLE => '1',
        DATA   => s_rand_data
    );

    s_rand_wr_addr <= s_rand_data(ADDR_GEN_WIDTH-2 downto 0) & '0';
    s_rand_rd_addr <= s_rand_data(ADDR_GEN_WIDTH downto 2) & '0';

    -- -------------------------------------------------------------------------
    --  SEQUENTIAL ADDRESS GENERATOR
    -- -------------------------------------------------------------------------

    s_sequ_wr_addr_en <= not s_gen_rw_switch when (CS_GEN_RW_SWITCH = '1') else '1';

    sequ_wr_addr_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_gen_run = '1') then
                if (WR_READY = '1' and s_gen_data_last = '1' and s_sequ_wr_addr_en = '1') then
                    s_sequ_wr_addr <= s_sequ_wr_addr + s_sequ_addr_inc;
                end if;
            else
                s_sequ_wr_addr <= (others => '0');
            end if;
        end if;
    end process;

    s_sequ_rd_addr_en <= s_gen_rw_switch when (CS_GEN_RW_SWITCH = '1') else '1';

    sequ_rd_addr_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_gen_run = '1') then
                if (RD_ADDR_READY = '1' and s_sequ_rd_addr_en = '1') then
                    s_sequ_rd_addr <= s_sequ_rd_addr + s_sequ_addr_inc;
                end if;
            else
                s_sequ_rd_addr <= (others => '0');
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  READ DATA CHECK
    -- -------------------------------------------------------------------------

    s_write_data_vld <= WR_VALID and WR_READY;
    s_read_data_vld  <= RD_DATA_VALID and RD_DATA_READY;

    s_data_cnt_rst <= RESET or not s_gen_run;

    data_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_data_cnt_rst = '1') then
                s_data_cnt <= (others => '0');
            elsif (s_write_data_vld = '1') then
                s_data_cnt <= s_data_cnt + 1;
            end if;
        end if;
    end process;

    data_cnt2_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_data_cnt_rst = '1') then
                s_data_cnt2 <= (others => '0');
            elsif (s_read_data_vld = '1') then
                s_data_cnt2 <= s_data_cnt2 + 1;
            end if;
        end if;
    end process;

    s_data_ok <= '1' when (unsigned(RD_DATA(7 downto 0)) = s_data_cnt2) else '0';

    STAT_DATA_OK_INC <= s_data_ok and s_read_data_vld;
    STAT_DATA_ERR_INC <= not s_data_ok and s_read_data_vld;

    -- -------------------------------------------------------------------------
    --  OUTPUT HSI SIGNALS ASSIGNMENT
    -- -------------------------------------------------------------------------

    wr_data_p : process (CS_GEN_WR_DEAD, s_data_cnt)
    begin
        if (CS_GEN_WR_DEAD = '1') then
            wr_data_dead_l : for i in 0 to (USR_DATA_WIDTH/32)-1 loop
                WR_DATA((i+1)*32-1 downto i*32) <= X"DEADCAFE";
            end loop;
        else
            WR_DATA <= (others => '0');
            WR_DATA(7 downto 0) <= std_logic_vector(s_data_cnt);
        end if;
    end process;

    wr_port_addr_g: if PORT_ADDR_WIDTH > 0 generate
        WR_ADDR(AXI_ADDR_WIDTH-1 downto PORT_ADDR_HBIT) <= std_logic_vector(to_unsigned(PORT_ID, PORT_ADDR_WIDTH)); -- Port Address Bits
    end generate;
    WR_ADDR(PORT_ADDR_HBIT-1 downto 5) <= s_rand_wr_addr when (CS_GEN_ADDR_MODE = '1') else std_logic_vector(s_sequ_wr_addr);
    WR_ADDR(4 downto 0)                <= (others => '0'); -- Unused Address Bits
    WR_DATA_LAST <= s_gen_data_last;
    WR_VALID     <= s_gen_run and CS_GEN_RUN_MODE(0) and s_sequ_wr_addr_en;
    WR_RSP_READY <= '1';

    rd_port_addr_g: if PORT_ADDR_WIDTH > 0 generate
        RD_ADDR(AXI_ADDR_WIDTH-1 downto PORT_ADDR_HBIT) <= std_logic_vector(to_unsigned(PORT_ID, PORT_ADDR_WIDTH)); -- Port Address Bits
    end generate;
    RD_ADDR(PORT_ADDR_HBIT-1 downto 5) <= s_rand_rd_addr when (CS_GEN_ADDR_MODE = '1') else std_logic_vector(s_sequ_rd_addr);
    RD_ADDR(4 downto 0)                <= (others => '0'); -- Unused Address Bits
    RD_ADDR_VALID <= s_gen_run and CS_GEN_RUN_MODE(1) and s_sequ_rd_addr_en;
    RD_DATA_READY <= '1';

end architecture;
