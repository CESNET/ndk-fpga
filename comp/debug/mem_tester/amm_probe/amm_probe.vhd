-- amm_probe.vhd: Component for moitoring AMM bus
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.hist_types.all;

-- MI ADDRESS SPACE --
-- ----------------------------------
-- ctrl                 BASE
--              R       0. in   - reset
--                      1. in   - latency: req -> first data [default: req -> last data]
--                      2. out  - write ticks                  overflow occured
--                      3. out  - read  ticks                  overflow occured
--                      4. out  - r/w   ticks                  overflow occured
--                      5. out  - write words                  overflow occured
--                      6. out  - read  words                  overflow occured
--                      7. out  - req   cnt                    overflow occured
--                      8. out  - latency ticks                overflow occured
--                      9. out  - latency counters             overflow occured
--                      10. out - latency sum                  overflow occured
--                      11. out - latency histogramer counters overflow occured
--                      12. out - latency histogramer is LINEAR (else LOG)
-- *(R = bit is rising edge triggered)
-- ----------------------------------
-- write ticks          BASE + 0x04
-- ----------------------------------
-- read  ticks          BASE + 0x08
-- ----------------------------------
-- r/w   ticks          BASE + 0x0C
--                      ticks of the whole communication
-- ----------------------------------
-- words written        BASE + 0x10
-- ----------------------------------
-- words read           BASE + 0x14
-- ----------------------------------
-- requests made        BASE + 0x18
-- ----------------------------------
-- latency sum          BASE + 0x1C
--                      BASE + 0x20
-- ----------------------------------
-- latency min          BASE + 0x24
-- ----------------------------------
-- latency max          BASE + 0x28
-- ----------------------------------
-- latency hist cnt     BASE + 0x2C
-- ----------------------------------
-- latency hist sel     BASE + 0x30
-- ----------------------------------
-- AMM data width reg   BASE + 0x34
-- -----------------------------------
-- AMM addr width reg   BASE + 0x38
-- -----------------------------------
-- AMM burst width reg  BASE + 0x3C
-- -----------------------------------
-- AMM freq reg [kHz]   BASE + 0x40
-- -----------------------------------
-- latency ticks width  BASE + 0x44
--                      For histogramer select signal (in LOG mode)
-- -----------------------------------
-- hist cnter cnt       BASE + 0x48
--                      For histogramer in LINEAR mode
-- -----------------------------------
-- Check register bases in mem-tester when adding new registers


-- Measurement start at first r/w request
-- Results can be cleared by RST signal or in ctrl register form MI bus

-- TODO:
-- Hangle change in burst count while response is running

entity AMM_PROBE is
generic (
    -- ================
    -- MI bus
    -- ================

    MI_DATA_WIDTH           : integer := 32;
    MI_ADDR_WIDTH           : integer := 32;

    -- ================
    -- Avalon bus
    -- ================

    AMM_DATA_WIDTH          : integer := 512;
    AMM_ADDR_WIDTH          : integer := 26;
    AMM_BURST_COUNT_WIDTH   : integer := 7;
    AMM_FREQ_KHZ            : integer := 266660;

    -- ================
    -- Others
    -- ================

    AMM_PIPE_REGS           : integer := 1;
    MI_ADDR_BASE            : std_logic_vector(MI_ADDR_WIDTH - 1 downto 0) := (others => '0');
    -- Number of used MI addr LSB bits
    MI_ADDR_USED_BITS       : integer := MI_ADDR_WIDTH;
    HISTOGRAM_BOXES         : integer := 512;
    DEVICE                  : string
);
port(
    -- ================
    -- Main
    -- ================

    CLK                     : in std_logic;
    RST                     : in std_logic;

    -- ================
    -- MI bus interface
    -- ================

    MI_DWR                  : in  std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    MI_ADDR                 : in  std_logic_vector(MI_ADDR_WIDTH - 1 downto 0);
    MI_BE                   : in  std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0);
    MI_RD                   : in  std_logic;
    MI_WR                   : in  std_logic;
    MI_ARDY                 : out std_logic;
    MI_DRD                  : out std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    MI_DRDY                 : out std_logic;

    -- ================
    -- Avalon interface
    -- ================

    AMM_READY               : in  std_logic;
    AMM_READ                : in  std_logic;
    AMM_WRITE               : in  std_logic;
    AMM_ADDRESS             : in  std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
    AMM_READ_DATA           : in  std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    AMM_WRITE_DATA          : in  std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    AMM_BURST_COUNT         : in  std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    AMM_READ_DATA_VALID     : in  std_logic
);
end entity;

-- =========================================================================

architecture FULL of AMM_PROBE is

    -- MI BUS --
    -- Core
    constant MI_ADDR_CUTOFF             : integer := log2(MI_DATA_WIDTH / 8);

    -- Registers
    constant CTRL_REG_ID                : integer := 0;
    constant WR_TICKS_REG_ID            : integer := 1;
    constant RD_TICKS_REG_ID            : integer := 2;
    constant RW_TICKS_REG_ID            : integer := 3;
    constant WR_WORDS_REG_ID            : integer := 4;
    constant RD_WORDS_REG_ID            : integer := 5;
    constant REQ_CNT_REG_ID             : integer := 6;
    constant LATENCY_SUM_REG_1_ID       : integer := 7;
    constant LATENCY_SUM_REG_2_ID       : integer := 8;
    constant LATENCY_MIN_REG_ID         : integer := 9;
    constant LATENCY_MAX_REG_ID         : integer := 10;
    constant LATENCY_HIST_CNT_ID        : integer := 11;
    constant LATENCY_HIST_SEL_ID        : integer := 12;
    constant AMM_DATA_W_REG_ID          : integer := 13;
    constant AMM_ADDR_W_REG_ID          : integer := 14;
    constant AMM_BURST_W_REG_ID         : integer := 15;
    constant AMM_FREQ_REG_ID            : integer := 16;
    constant LATENCY_TICKS_WIDTH_ID     : integer := 17;
    constant HIST_CNTER_CNT_ID          : integer := 18;

    -- Bits - IN
    constant RST_BIT                    : integer := 0;
    constant LATENCY_TO_FIRST_BIT       : integer := 1;

    -- Bits - OUT
    constant WR_TICKS_OVF_BIT           : integer := 2;
    constant RD_TICKS_OVF_BIT           : integer := 3;
    constant RW_TICKS_OVF_BIT           : integer := 4;
    constant WR_WORDS_OVF_BIT           : integer := 5;
    constant RD_WORDS_OVF_BIT           : integer := 6;
    constant REQ_CNT_OVF_BIT            : integer := 7;
    constant LATENCY_TICKS_OVF_BIT      : integer := 8;
    constant LATENCY_CNTERS_OVF_BIT     : integer := 9;
    constant LATENCY_SUM_OVF_BIT        : integer := 10;
    constant LATENCY_HIST_OVF_BIT       : integer := 11;
    constant HIST_IS_LINEAR_BIT         : integer := 12;

    -- Bits - constants
    constant CTRL_LAST_IN_BIT           : integer := LATENCY_TO_FIRST_BIT;
    constant CTRL_LAST_OUT_BIT          : integer := HIST_IS_LINEAR_BIT;

    -- PROBE --
    -- If larger ticks counters needed, one must break down data into multiple MI regs
    constant TICKS_WIDTH                : integer := MI_DATA_WIDTH;
    constant TICKS_LIMIT                : unsigned(TICKS_WIDTH - 1 downto 0) := (others => '1');

    constant WORDS_CNT_WIDTH            : integer := MI_DATA_WIDTH;
    constant WORDS_CNT_LIMIT            : unsigned(WORDS_CNT_WIDTH - 1 downto 0) := (others => '1');

    -- Max latency ticks = 4095 => with freq = 333.33 Mhz => max. latency = 12us
    constant LATENCY_TICKS_WIDTH        : integer := 12;
    constant LATENCY_SUM_WIDTH          : integer := MI_DATA_WIDTH * 2;
    -- TODO
    constant LATENCY_COUNTERS_CNT       : integer := 128;

    constant HIST_VARIANT               : HIST_T  := LINEAR;
    -- When LOG hist used => set to LATENCY_TICKS_WIDTH
    -- TODO
    constant HIST_CNTER_CNT             : integer := HISTOGRAM_BOXES;
    constant HIST_CNT_WIDTH             : integer := MI_DATA_WIDTH;

    -- ----------------------------------------------------------------------- --

    function id_to_addr_f (addr : integer)
    return std_logic_vector is
        constant mi_addr_base_int   : integer := to_integer(unsigned(MI_ADDR_BASE(MI_ADDR_USED_BITS - 1 downto MI_ADDR_CUTOFF)));
    begin
        return std_logic_vector(to_unsigned(mi_addr_base_int + addr, MI_ADDR_USED_BITS - MI_ADDR_CUTOFF));
    end function;

    -- ----------------------------------------------------------------------- --

    -- CORE --
    signal total_rst_raw                : std_logic;    -- Without delay register
    signal total_rst                    : std_logic;

    -- MI BUS --
    -- Selection mechanism
    signal mi_addr_sliced               : std_logic_vector(MI_ADDR_USED_BITS - 1 downto MI_ADDR_CUTOFF);
    -- Registers
    signal ctrl_reg                     : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal wr_ticks_reg                 : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal rd_ticks_reg                 : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal rw_ticks_reg                 : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    -- Bits
    signal mi_rst_req_raw               : std_logic;    -- Without edge trig
    signal mi_rst_req                   : std_logic;

    -- AMM BUS --
    -- Pipe (pipe(0) = original)
    signal amm_pipe_ready               : std_logic_vector(AMM_PIPE_REGS downto 0);
    signal amm_pipe_read                : std_logic_vector(AMM_PIPE_REGS downto 0);
    signal amm_pipe_write               : std_logic_vector(AMM_PIPE_REGS downto 0);
    signal amm_pipe_address             : slv_array_t(AMM_PIPE_REGS downto 0)(AMM_ADDR_WIDTH - 1 downto 0);
    signal amm_pipe_read_data           : slv_array_t(AMM_PIPE_REGS downto 0)(AMM_DATA_WIDTH - 1 downto 0);
    signal amm_pipe_write_data          : slv_array_t(AMM_PIPE_REGS downto 0)(AMM_DATA_WIDTH - 1 downto 0);
    signal amm_pipe_burst_count         : slv_array_t(AMM_PIPE_REGS downto 0)(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    signal amm_pipe_read_data_valid     : std_logic_vector(AMM_PIPE_REGS downto 0);
    -- Intern
    signal amm_intern_ready             : std_logic;
    signal amm_intern_read              : std_logic;
    signal amm_intern_write             : std_logic;
    signal amm_intern_address           : std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
    signal amm_intern_read_data         : std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    signal amm_intern_write_data        : std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    signal amm_intern_burst_count       : std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    signal amm_intern_read_data_valid   : std_logic;
    -- Logic
    signal amm_wr_req                   : std_logic;
    signal amm_rd_req                   : std_logic;
    signal amm_rd_resp                  : std_logic;
    -- Counters
    -- Burst counters start at 1 to match AMM_BURST_COUNT
    signal wr_burst                     : unsigned(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    signal wr_burst_done                : std_logic;
    signal rd_burst                     : unsigned(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    signal rd_burst_done                : std_logic;
    signal rd_burst_start               : std_logic;

    -- PROBE --
    signal wr_ticks                     : unsigned(TICKS_WIDTH - 1 downto 0);
    signal wr_ticks_full                : std_logic;
    signal wr_ticks_en                  : std_logic;
    signal wr_ticks_en_delayed          : std_logic;
    signal wr_ticks_ovf_occ             : std_logic;

    signal rd_ticks                     : unsigned(TICKS_WIDTH - 1 downto 0);
    signal rd_ticks_full                : std_logic;
    signal rd_ticks_en                  : std_logic;
    signal rd_ticks_en_delayed          : std_logic;
    signal rd_ticks_ovf_occ             : std_logic;

    signal rw_ticks                     : unsigned(TICKS_WIDTH - 1 downto 0);
    signal rw_ticks_full                : std_logic;
    signal rw_ticks_en                  : std_logic;
    signal rw_ticks_en_delayed          : std_logic;
    signal rw_ticks_ovf_occ             : std_logic;

    signal wr_words                     : unsigned(WORDS_CNT_WIDTH - 1 downto 0);
    signal wr_words_full                : std_logic;
    signal wr_words_ovf_occ             : std_logic;

    signal rd_words                     : unsigned(WORDS_CNT_WIDTH - 1 downto 0);
    signal rd_words_full                : std_logic;
    signal rd_words_ovf_occ             : std_logic;

    signal req_cnt                      : unsigned(WORDS_CNT_WIDTH - 1 downto 0);
    signal req_cnt_full                 : std_logic;
    signal req_cnt_ovf_occ              : std_logic;

    signal latency_sum_ticks            : std_logic_vector(LATENCY_SUM_WIDTH - 1 downto 0);
    signal latency_min_ticks            : std_logic_vector(LATENCY_TICKS_WIDTH - 1 downto 0);
    signal latency_max_ticks            : std_logic_vector(LATENCY_TICKS_WIDTH - 1 downto 0);

    signal latency_hist_sel_cnter       : std_logic_vector(log2(HIST_CNTER_CNT) - 1 downto 0);
    signal latency_hist_cnt             : std_logic_vector(HIST_CNT_WIDTH - 1 downto 0);

    signal latency_ticks_ovf            : std_logic;
    signal latency_counters_ovf         : std_logic;
    signal latency_sum_ovf              : std_logic;
    signal latency_hist_cnt_ovf         : std_logic;

    signal latency_ticks_ovf_occ        : std_logic;
    signal latency_counters_ovf_occ     : std_logic;
    signal latency_sum_ovf_occ          : std_logic;

    -- 1 = measure latency to first received data, 0 = to last received data
    signal latency_to_first_word        : std_logic;
    signal latency_meter_resp           : std_logic;

begin

    -- ----------------------------------------------------------------------- --

    -------------------------
    -- Component instances --
    -------------------------
    rst_edge_trig_i : entity work.EDGE_DETECT
    port map (
        CLK                 => CLK,
        DI                  => mi_rst_req_raw,
        EDGE                => mi_rst_req
    );

    latency_meter_old_i : entity work.LATENCY_METER_OLD
    generic map (
        TICKS_WIDTH         => LATENCY_TICKS_WIDTH,
        SUM_WIDTH           => LATENCY_SUM_WIDTH,
        COUNTERS_CNT        => LATENCY_COUNTERS_CNT,

        HIST_VARIANT        => HIST_VARIANT  ,
        HIST_CNTER_CNT      => HIST_CNTER_CNT,
        HIST_CNT_WIDTH      => HIST_CNT_WIDTH
    )
    port map (
        CLK                 => CLK,
        RST                 => total_rst,

        READ_REQ            => amm_rd_req,
        READ_RESP           => latency_meter_resp,

        SUM_TICKS           => latency_sum_ticks,
        MIN_TICKS           => latency_min_ticks,
        MAX_TICKS           => latency_max_ticks,

        HIST_CNT            => latency_hist_cnt,
        HIST_SEL_CNTER      => latency_hist_sel_cnter,

        TICKS_OVF           => latency_ticks_ovf,
        COUNTERS_OVF        => latency_counters_ovf,
        SUM_OVF             => latency_sum_ovf,
        HIST_CNT_OVF        => latency_hist_cnt_ovf
    );

    -------------------------
    -- Combinational logic --
    -------------------------
    -- CORE --
    total_rst_raw                   <= RST or mi_rst_req;

    -- MI BUS --
    -- Selection mechanism
    mi_addr_sliced                  <= MI_ADDR(MI_ADDR_USED_BITS - 1 downto MI_ADDR_CUTOFF);
    -- Bits
    mi_rst_req_raw                  <= ctrl_reg(RST_BIT);
    latency_to_first_word           <= ctrl_reg(LATENCY_TO_FIRST_BIT);

    -- These are performed only on  a new r/w request
    ctrl_reg(WR_WORDS_OVF_BIT)      <= wr_words_ovf_occ;
    ctrl_reg(RD_WORDS_OVF_BIT)      <= rd_words_ovf_occ;
    ctrl_reg(REQ_CNT_OVF_BIT)       <= req_cnt_ovf_occ;
    ctrl_reg(LATENCY_TICKS_OVF_BIT ) <= latency_ticks_ovf_occ;
    ctrl_reg(LATENCY_CNTERS_OVF_BIT) <= latency_counters_ovf_occ;
    ctrl_reg(LATENCY_SUM_OVF_BIT)   <= latency_sum_ovf_occ;
    ctrl_reg(LATENCY_HIST_OVF_BIT)  <= latency_hist_cnt_ovf;
    ctrl_reg(HIST_IS_LINEAR_BIT)    <= '1' when (HIST_VARIANT = LINEAR) else
                                       '0';

    -- Ready signals
    MI_ARDY                         <= MI_RD or MI_WR;

    -- AMM BUS --
    -- Pipe
    amm_pipe_ready          (0)     <= AMM_READY          ;
    amm_pipe_read           (0)     <= AMM_READ           ;
    amm_pipe_write          (0)     <= AMM_WRITE          ;
    amm_pipe_address        (0)     <= AMM_ADDRESS        ;
    amm_pipe_read_data      (0)     <= AMM_READ_DATA      ;
    amm_pipe_write_data     (0)     <= AMM_WRITE_DATA     ;
    amm_pipe_burst_count    (0)     <= AMM_BURST_COUNT    ;
    amm_pipe_read_data_valid(0)     <= AMM_READ_DATA_VALID;

    amm_intern_ready                <= amm_pipe_ready          (AMM_PIPE_REGS);
    amm_intern_read                 <= amm_pipe_read           (AMM_PIPE_REGS);
    amm_intern_write                <= amm_pipe_write          (AMM_PIPE_REGS);
    amm_intern_address              <= amm_pipe_address        (AMM_PIPE_REGS);
    amm_intern_read_data            <= amm_pipe_read_data      (AMM_PIPE_REGS);
    amm_intern_write_data           <= amm_pipe_write_data     (AMM_PIPE_REGS);
    amm_intern_burst_count          <= amm_pipe_burst_count    (AMM_PIPE_REGS);
    amm_intern_read_data_valid      <= amm_pipe_read_data_valid(AMM_PIPE_REGS);

    -- Logic
    amm_wr_req                      <= amm_intern_write and amm_intern_ready;
    amm_rd_req                      <= amm_intern_read  and amm_intern_ready;
    amm_rd_resp                     <= amm_intern_read_data_valid;
    -- Counters done
    wr_burst_done                   <= '1' when (unsigned(AMM_BURST_COUNT) = wr_burst and amm_wr_req = '1') else
                                       '0';
    rd_burst_done                   <= '1' when (unsigned(AMM_BURST_COUNT) = rd_burst and amm_rd_resp = '1') else
                                       '0';
    rd_burst_start                  <= '1' when (rd_burst = 1 and amm_rd_resp = '1') else
                                       '0';

    -- PROBE --
    wr_ticks_en                     <= wr_ticks_en_delayed or amm_wr_req;
    rd_ticks_en                     <= rd_ticks_en_delayed or amm_rd_req;
    rw_ticks_en                     <= rw_ticks_en_delayed or amm_wr_req or amm_rd_req;

    wr_ticks_full                   <= '1' when(wr_ticks = TICKS_LIMIT and wr_ticks_en = '1') else
                                       '0';
    rd_ticks_full                   <= '1' when(rd_ticks = TICKS_LIMIT and rd_ticks_en = '1') else
                                       '0';
    rw_ticks_full                   <= '1' when(rw_ticks = TICKS_LIMIT and rw_ticks_en = '1') else
                                       '0';
    wr_words_full                   <= '1' when(wr_words = WORDS_CNT_LIMIT and amm_wr_req = '1') else
                                       '0';
    rd_words_full                   <= '1' when(rd_words = WORDS_CNT_LIMIT and amm_rd_resp = '1') else
                                       '0';
    req_cnt_full                    <= '1' when(req_cnt = WORDS_CNT_LIMIT and amm_rd_req = '1') else
                                       '0';

    latency_meter_resp              <= amm_rd_resp and rd_burst_done when (latency_to_first_word = '0') else
                                       amm_rd_resp and rd_burst_start;
    ---------------
    -- Registers --
    ---------------
    -- CORE --
    total_rst_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            total_rst   <= total_rst_raw;
        end if;
    end process;

    -- MI BUS --
    mi_out_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            -- Case can't be used because of warning:
            -- "case choice should be a locally static expression"
            if (mi_addr_sliced = id_to_addr_f(CTRL_REG_ID)          ) then
                MI_DRD <= ctrl_reg;
            elsif (mi_addr_sliced = id_to_addr_f(WR_TICKS_REG_ID)   ) then
                MI_DRD <= wr_ticks_reg;
            elsif (mi_addr_sliced = id_to_addr_f(RD_TICKS_REG_ID)   ) then
                MI_DRD <= rd_ticks_reg;
            elsif (mi_addr_sliced = id_to_addr_f(RW_TICKS_REG_ID)   ) then
                MI_DRD <= rw_ticks_reg;
            elsif (mi_addr_sliced = id_to_addr_f(WR_WORDS_REG_ID)   ) then
                MI_DRD <= std_logic_vector(wr_words);
            elsif (mi_addr_sliced = id_to_addr_f(RD_WORDS_REG_ID)   ) then
                MI_DRD <= std_logic_vector(rd_words);
            elsif (mi_addr_sliced = id_to_addr_f(REQ_CNT_REG_ID)    ) then
                MI_DRD <= std_logic_vector(req_cnt);
            elsif (mi_addr_sliced = id_to_addr_f(LATENCY_SUM_REG_1_ID)) then
                MI_DRD <= latency_sum_ticks(MI_DATA_WIDTH - 1 downto 0);
            elsif (mi_addr_sliced = id_to_addr_f(LATENCY_SUM_REG_2_ID)) then
                MI_DRD <= latency_sum_ticks(MI_DATA_WIDTH * 2 - 1 downto MI_DATA_WIDTH);
            elsif (mi_addr_sliced = id_to_addr_f(LATENCY_MIN_REG_ID)) then
                MI_DRD <=  (MI_DATA_WIDTH downto LATENCY_TICKS_WIDTH => '0') & latency_min_ticks;
            elsif (mi_addr_sliced = id_to_addr_f(LATENCY_MAX_REG_ID)) then
                MI_DRD <=  (MI_DATA_WIDTH downto LATENCY_TICKS_WIDTH => '0') & latency_max_ticks;
            elsif (mi_addr_sliced = id_to_addr_f(LATENCY_HIST_CNT_ID)) then
                MI_DRD <= (MI_DATA_WIDTH downto HIST_CNT_WIDTH => '0') & latency_hist_cnt;
            elsif (mi_addr_sliced = id_to_addr_f(LATENCY_HIST_SEL_ID)) then
                MI_DRD <= (MI_DATA_WIDTH downto log2(HIST_CNTER_CNT) - 1 => '0') & latency_hist_sel_cnter;

            -- Dev info registers
            elsif (mi_addr_sliced = id_to_addr_f(AMM_DATA_W_REG_ID) ) then
                MI_DRD <= std_logic_vector(to_unsigned(AMM_DATA_WIDTH,           MI_DATA_WIDTH));
            elsif (mi_addr_sliced = id_to_addr_f(AMM_ADDR_W_REG_ID) ) then
                MI_DRD <= std_logic_vector(to_unsigned(AMM_ADDR_WIDTH,           MI_DATA_WIDTH));
            elsif (mi_addr_sliced = id_to_addr_f(AMM_BURST_W_REG_ID)) then
                MI_DRD <= std_logic_vector(to_unsigned(AMM_BURST_COUNT_WIDTH,    MI_DATA_WIDTH));
            elsif (mi_addr_sliced = id_to_addr_f(AMM_FREQ_REG_ID)   ) then
                MI_DRD <= std_logic_vector(to_unsigned(AMM_FREQ_KHZ,             MI_DATA_WIDTH));
            elsif (mi_addr_sliced = id_to_addr_f(LATENCY_TICKS_WIDTH_ID)) then
                MI_DRD <= std_logic_vector(to_unsigned(LATENCY_TICKS_WIDTH,      MI_DATA_WIDTH));
            elsif (mi_addr_sliced = id_to_addr_f(HIST_CNTER_CNT_ID)) then
                MI_DRD <= std_logic_vector(to_unsigned(HIST_CNTER_CNT,           MI_DATA_WIDTH));

            else
                MI_DRD <= X"DEADBEEF";
            end if;
        end if;
    end process;

    mi_in_addr_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                ctrl_reg(CTRL_LAST_IN_BIT downto 0)                         <= (others => '0');
                ctrl_reg(MI_DATA_WIDTH - 1 downto CTRL_LAST_OUT_BIT + 1)    <= (others => '0');
                latency_hist_sel_cnter                                      <= (others => '0');
            elsif (MI_WR = '1') then
                if (mi_addr_sliced = id_to_addr_f(CTRL_REG_ID)) then
                    ctrl_reg(CTRL_LAST_IN_BIT downto 0)  <= MI_DWR(CTRL_LAST_IN_BIT downto 0);
                elsif (mi_addr_sliced = id_to_addr_f(LATENCY_HIST_SEL_ID)) then
                    latency_hist_sel_cnter  <= MI_DWR(latency_hist_sel_cnter'length - 1 downto 0);
                end if;
            end if;
        end if;
    end process;

    mi_drdy_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            MI_DRDY <= MI_RD;
        end if;
    end process;

    --- AMM BUS --
    -- Pipe
    amm_pipe_g : for i in 0 to AMM_PIPE_REGS - 1 generate
        amm_pipe_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                amm_pipe_ready          (i + 1)    <= amm_pipe_ready          (i);
                amm_pipe_read           (i + 1)    <= amm_pipe_read           (i);
                amm_pipe_write          (i + 1)    <= amm_pipe_write          (i);
                amm_pipe_address        (i + 1)    <= amm_pipe_address        (i);
                amm_pipe_read_data      (i + 1)    <= amm_pipe_read_data      (i);
                amm_pipe_write_data     (i + 1)    <= amm_pipe_write_data     (i);
                amm_pipe_burst_count    (i + 1)    <= amm_pipe_burst_count    (i);
                amm_pipe_read_data_valid(i + 1)    <= amm_pipe_read_data_valid(i);
            end if;
        end process;
    end generate;

    -- Burst counters
    wr_burst_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1' or (wr_burst_done = '1' and amm_wr_req = '1')) then
                wr_burst    <= to_unsigned(1, AMM_BURST_COUNT_WIDTH);
            elsif (amm_wr_req = '1') then
                wr_burst    <= wr_burst + 1;
            end if;
        end if;
    end process;

    rd_burst_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1' or (rd_burst_done = '1' and amm_rd_resp = '1')) then
                rd_burst    <= to_unsigned(1, AMM_BURST_COUNT_WIDTH);
            elsif (amm_rd_resp = '1') then
                rd_burst    <= rd_burst + 1;
            end if;
        end if;
    end process;

    -- PROBE --
    -- R/W ticks counters
    wr_ticks_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1' or (wr_ticks_full = '1' and wr_ticks_en = '1')) then
                wr_ticks    <= to_unsigned(1, TICKS_WIDTH);
            elsif (wr_ticks_en = '1') then
                wr_ticks    <= wr_ticks + 1;
            end if;
        end if;
    end process;

   rd_ticks_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1' or (rd_ticks_full = '1' and rd_ticks_en = '1')) then
                rd_ticks    <= to_unsigned(1, TICKS_WIDTH);
            elsif (rd_ticks_en = '1') then
                rd_ticks    <= rd_ticks + 1;
            end if;
        end if;
    end process;

   rw_ticks_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1' or (rw_ticks_full = '1' and rw_ticks_en = '1')) then
                rw_ticks    <= to_unsigned(1, TICKS_WIDTH);
            elsif (rw_ticks_en = '1') then
                rw_ticks    <= rw_ticks + 1;
            end if;
        end if;
    end process;

    -- R/W tick EN (enable ticks counters on first r/w request)
    wr_ticks_en_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                wr_ticks_en_delayed <= '0';
            elsif (amm_wr_req = '1') then
                wr_ticks_en_delayed <= '1';
            end if;
        end if;
    end process;

    rd_ticks_en_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                rd_ticks_en_delayed <= '0';
            elsif (amm_rd_req = '1') then
                rd_ticks_en_delayed <= '1';
            end if;
        end if;
    end process;

    rw_ticks_en_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                rw_ticks_en_delayed <= '0';
            elsif (amm_wr_req = '1' or amm_rd_req = '1') then
                rw_ticks_en_delayed <= '1';
            end if;
        end if;
    end process;

    -- R/W ticks overflow occured
    wr_ticks_ovf_occ_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                wr_ticks_ovf_occ    <= '0';
            elsif (wr_ticks_full = '1') then
                wr_ticks_ovf_occ    <= '1';
            end if;
        end if;
    end process;

    rd_ticks_ovf_occ_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                rd_ticks_ovf_occ    <= '0';
            elsif (rd_ticks_full = '1') then
                rd_ticks_ovf_occ    <= '1';
            end if;
        end if;
    end process;

    rw_ticks_ovf_occ_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                rw_ticks_ovf_occ    <= '0';
            elsif (rw_ticks_full = '1') then
                rw_ticks_ovf_occ    <= '1';
            end if;
        end if;
    end process;

    -- Save r/w ticks to mi regs only on r/w request (only last req ticks will be saved)
    -- Counter will be then still running
    wr_ticks_save_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                wr_ticks_reg                <= (others => '0');
                ctrl_reg(WR_TICKS_OVF_BIT)  <= '0';
            elsif (amm_wr_req = '1') then
                wr_ticks_reg                <= std_logic_vector(wr_ticks);
                ctrl_reg(WR_TICKS_OVF_BIT)  <= wr_ticks_ovf_occ;
            end if;
        end if;
    end process;

    rd_ticks_save_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                rd_ticks_reg                <= (others => '0');
                ctrl_reg(RD_TICKS_OVF_BIT)  <= '0';
            elsif (amm_rd_req = '1' or amm_rd_resp = '1') then
                rd_ticks_reg                <= std_logic_vector(rd_ticks);
                ctrl_reg(RD_TICKS_OVF_BIT)  <= rd_ticks_ovf_occ;
            end if;
        end if;
    end process;

    rw_ticks_save_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                rw_ticks_reg                <= (others => '0');
                ctrl_reg(RW_TICKS_OVF_BIT)  <= '0';
            elsif (amm_wr_req = '1' or amm_rd_req = '1' or amm_rd_resp = '1') then
                rw_ticks_reg                <= std_logic_vector(rw_ticks);
                ctrl_reg(RW_TICKS_OVF_BIT)  <= rw_ticks_ovf_occ;
            end if;
        end if;
    end process;

    -- Words counters
    wr_words_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1' or wr_words_full = '1') then
                wr_words    <= (others => '0');
            elsif (amm_wr_req = '1') then
                wr_words    <= wr_words + 1;
            end if;
        end if;
    end process;

    rd_words_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1' or rd_words_full = '1') then
                rd_words    <= (others => '0');
            elsif (amm_rd_resp = '1') then
                rd_words    <= rd_words + 1;
            end if;
        end if;
    end process;

    wr_words_ovf_occ_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                wr_words_ovf_occ    <= '0';
            elsif (wr_words_full = '1') then
                wr_words_ovf_occ    <= '1';
            end if;
        end if;
    end process;

    rd_words_ovf_occ_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                rd_words_ovf_occ    <= '0';
            elsif (rd_words_full = '1') then
                rd_words_ovf_occ    <= '1';
            end if;
        end if;
    end process;

    req_cnt_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1' or req_cnt_full = '1') then
                req_cnt    <= (others => '0');
            elsif (amm_rd_req = '1') then
                req_cnt    <= req_cnt + 1;
            end if;
        end if;
    end process;

    req_cnt_ovf_occ_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                req_cnt_ovf_occ    <= '0';
            elsif (req_cnt_full = '1') then
                req_cnt_ovf_occ    <= '1';
            end if;
        end if;
    end process;

    latency_ticks_ovf_occ_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                latency_ticks_ovf_occ   <= '0';
            elsif (latency_ticks_ovf = '1') then
                latency_ticks_ovf_occ   <= '1';
            end if;
        end if;
    end process;

    latency_counters_ovf_occ_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                latency_counters_ovf_occ   <= '0';
            elsif (latency_counters_ovf = '1') then
                latency_counters_ovf_occ   <= '1';
            end if;
        end if;
    end process;

    latency_sum_ovf_occ_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (total_rst = '1') then
                latency_sum_ovf_occ   <= '0';
            elsif (latency_sum_ovf = '1') then
                latency_sum_ovf_occ   <= '1';
            end if;
        end if;
    end process;
end architecture;
