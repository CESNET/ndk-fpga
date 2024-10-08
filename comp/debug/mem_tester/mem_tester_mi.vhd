-- mem_tester_mi.vhd: Subcomponent for mem_tester component
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- MI ADDRESS SPACE --
-- ----------------------------------
-- Addr    bit     dir    content
-- ----------------------------------
-- ctrl in reg
-- 0X00    0.      in      reset
--         1.      in      reset EMIF IP
--         2.      in      run test
--         3.      in      amm_gen enable
--         4.      in      random addressing during test
--         5.      in      only 1 simultaneous read transaction
--         6.      in      auto precharge req
-- ctrl out reg
-- 0X04    0.      out     test done
--         1.      out     test succesfull
--         2.      out     ecc err occured
--         3.      out     calib successful
--         4.      out     calib failed
--         5.      out     amm ready
-- ----------------------------------
-- err cnt reg
-- 0X08    all     out     err cnt
-- -----------------------------------
-- burst cnt reg
-- 0X0C    all     out     set burst cnt of mi transactions (1-127)
-- -----------------------------------
-- addr lim reg
-- 0X10    all     i/o     last address that will be tested (must be multiple of burst cnt)
-- ----------------------------------
-- refresh period reg
-- 0X14    all     i/o     refresh period ticks when manual refresh is used
-- ----------------------------------
-- default refresh period reg
-- 0X18    all     o
-- ----------------------------------
-- amm_gen
-- AMM_GEN_BASE
-- ----------------------------------
-- amm_probe
-- AMM_PROBE_BASE
-- ----------------------------------

entity MEM_TESTER_MI is
generic (
    -- ================
    -- Buses
    -- ================

    MI_DATA_WIDTH           : integer := 32;
    MI_ADDR_WIDTH           : integer := 32;
    AMM_ADDR_WIDTH          : integer := 26;
    AMM_BURST_COUNT_WIDTH   : integer := 7;
    REFR_PERIOD_WIDTH       : integer := 32;

    -- ================
    -- Others
    -- ================

    AMM_GEN_BASE            : std_logic_vector(MI_ADDR_WIDTH - 1 downto 0);
    AMM_PROBE_BASE          : std_logic_vector(MI_ADDR_WIDTH - 1 downto 0);
    DEFAULT_BURST_CNT       : integer := 4;
    DEFAULT_ADDR_LIMIT      : integer;
    DEF_REFR_PERIOD         : std_logic_vector(REFR_PERIOD_WIDTH - 1 downto 0);
    DEVICE                  : string
);
port(
    -- ==========================
    -- MI bus master interface
    -- ==========================

    MI_CLK                  : in std_logic;
    MI_RST                  : in std_logic;

    MI_DWR                  : in  std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    MI_ADDR                 : in  std_logic_vector(MI_ADDR_WIDTH - 1 downto 0);
    MI_BE                   : in  std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0);
    MI_RD                   : in  std_logic;
    MI_WR                   : in  std_logic;
    MI_ARDY                 : out std_logic;
    MI_DRD                  : out std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    MI_DRDY                 : out std_logic;

    -- ==========================
    -- Slave clk and rst
    -- ==========================

    CLK                     : in std_logic;
    RST                     : in std_logic;

    -- ==========================
    -- Signals to / from slave
    --
    -- Master => slave
    -- ==========================

    RST_REQ                 : out std_logic;
    RST_EMIF_REQ            : out std_logic;
    RUN_TEST                : out std_logic;
    MANUAL_EN               : out std_logic;
    RANDOM_ADDR_EN          : out std_logic;
    ONE_SIMULT_READ         : out std_logic;
    AUTO_PRECHARGE          : out std_logic;
    BURST_CNT               : out std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    ADDR_LIMIT              : out std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
    REFR_PERIOD             : out std_logic_vector(REFR_PERIOD_WIDTH - 1 downto 0);

    -- ==========================
    -- Signals to / from slave
    --
    -- Slave => master
    -- ==========================

    TEST_DONE               : in  std_logic;
    TEST_SUCCESS            : in  std_logic;
    ECC_ERROR               : in  std_logic;
    CALIB_SUCCESS           : in  std_logic;
    CALIB_FAIL              : in  std_logic;
    AMM_READY               : in  std_logic;
    ERR_CNT                 : in  std_logic_vector(MI_DATA_WIDTH - 1 downto 0);

    -- ==========================
    -- AMM GEN MI bus
    -- ==========================

    AMM_GEN_DWR             : out std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    AMM_GEN_ADDR            : out std_logic_vector(MI_ADDR_WIDTH - 1 downto 0);
    AMM_GEN_BE              : out std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0);
    AMM_GEN_RD              : out std_logic;
    AMM_GEN_WR              : out std_logic;
    AMM_GEN_ARDY            : in  std_logic;
    AMM_GEN_DRD             : in  std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    AMM_GEN_DRDY            : in  std_logic;

    -- ==========================
    -- AMM PROBE MI bus
    -- ==========================

    AMM_PROBE_DWR           : out std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    AMM_PROBE_ADDR          : out std_logic_vector(MI_ADDR_WIDTH - 1 downto 0);
    AMM_PROBE_BE            : out std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0);
    AMM_PROBE_RD            : out std_logic;
    AMM_PROBE_WR            : out std_logic;
    AMM_PROBE_ARDY          : in  std_logic;
    AMM_PROBE_DRD           : in  std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    AMM_PROBE_DRDY          : in  std_logic
);
end entity;

architecture FULL of MEM_TESTER_MI is

    -- MI SPLITTER
    constant MI_PORTS           : integer := 3;

    constant MI_BASE_PORT       : integer := 2;
    constant AMM_GEN_PORT       : integer := 1;
    constant AMM_PROBE_PORT     : integer := 0;

    constant ADDR_BASES         : slv_array_t(MI_PORTS - 1 downto 0)(MI_ADDR_WIDTH - 1 downto 0) :=
        (
            2 => AMM_PROBE_BASE,
            1 => AMM_GEN_BASE,
            0 => std_logic_vector(to_unsigned(0, MI_ADDR_WIDTH))
        );

    -- MI sliced
    constant MI_ADDR_CUTOFF     : integer := log2(MI_DATA_WIDTH / 8);
    constant MI_ADDR_LIMIT      : integer := 7;

    -- MI registers addresses --
    -- 0x00
    constant CTRL_IN_REG        : std_logic_vector(MI_ADDR_LIMIT downto MI_ADDR_CUTOFF) := "000000";
    -- 0x04
    constant CTRL_OUT_REG       : std_logic_vector(MI_ADDR_LIMIT downto MI_ADDR_CUTOFF) := "000001";
    -- 0x08
    constant ERR_CNT_REG        : std_logic_vector(MI_ADDR_LIMIT downto MI_ADDR_CUTOFF) := "000010";
    -- 0x0C
    constant BURST_CNT_REG      : std_logic_vector(MI_ADDR_LIMIT downto MI_ADDR_CUTOFF) := "000011";
    -- 0x10
    constant ADDR_LIM_REG       : std_logic_vector(MI_ADDR_LIMIT downto MI_ADDR_CUTOFF) := "000100";
    -- 0x14
    constant REFRESH_TICKS_REG  : std_logic_vector(MI_ADDR_LIMIT downto MI_ADDR_CUTOFF) := "000101";
    -- 0x18
    constant DEF_REFR_REG       : std_logic_vector(MI_ADDR_LIMIT downto MI_ADDR_CUTOFF) := "000110";

    -- Bits in registers
    -- CTRL IN REG
    constant RST_BIT            : integer := 0;
    constant RST_EMIF_BIT       : integer := 1;
    constant RUN_TEST_BIT       : integer := 2;
    constant MANUAL_EN_BIT      : integer := 3;
    constant RANDOM_ADDR_EN_BIT : integer := 4;
    constant ONE_SIMULT_READ_BIT : integer := 5;
    constant AUTO_PRECHARGE_BIT : integer := 6;

    -- CTRL OUT REG
    constant TEST_DONE_BIT      : integer := 0;
    constant TEST_SUCCESS_BIT   : integer := 1;
    constant ECC_ERROR_BIT      : integer := 2;
    constant CALIB_SUCCESS_BIT  : integer := 3;
    constant CALIB_FAIL_BIT     : integer := 4;
    constant AMM_READY_BIT      : integer := 5;

    ------------
    -- MI bus --
    ------------

    -- MI interface synchronized to slave clk domain
    signal mi_dwr_sync          : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal mi_addr_sync         : std_logic_vector(MI_ADDR_WIDTH - 1 downto 0);
    signal mi_be_sync           : std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0);
    signal mi_rd_sync           : std_logic;
    signal mi_wr_sync           : std_logic;
    signal mi_ardy_sync         : std_logic;
    signal mi_drd_sync          : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal mi_drdy_sync         : std_logic;

    -- MI ports (from MI splitter)
    signal mi_splitted_addr     : slv_array_t(0 to MI_PORTS - 1)(MI_ADDR_WIDTH - 1 downto 0);
    signal mi_splitted_dwr      : slv_array_t(0 to MI_PORTS - 1)(MI_DATA_WIDTH - 1 downto 0);
    signal mi_splitted_drd      : slv_array_t(0 to MI_PORTS - 1)(MI_DATA_WIDTH - 1 downto 0);
    signal mi_splitted_be       : slv_array_t(0 to MI_PORTS - 1)(MI_DATA_WIDTH / 8 - 1 downto 0);
    signal mi_splitted_rd       : std_logic_vector(0 to MI_PORTS - 1);
    signal mi_splitted_wr       : std_logic_vector(0 to MI_PORTS - 1);
    signal mi_splitted_ardy     : std_logic_vector(0 to MI_PORTS - 1);
    signal mi_splitted_drdy     : std_logic_vector(0 to MI_PORTS - 1);

    -- Indicates which MI reg is currently selected
    signal sel_reg              : std_logic_vector(MI_ADDR_LIMIT downto MI_ADDR_CUTOFF);

    -- registers --
    signal ctrl_in              : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal ctrl_out             : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal burst_cnt_intern     : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal addr_lim_intern      : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal refresh_period_intern: std_logic_vector(MI_DATA_WIDTH - 1 downto 0);

    signal reset_raw            : std_logic;
    signal reset_emif_raw       : std_logic;
    signal run_test_raw         : std_logic;

begin
    -------------------------
    -- Component instances --
    -------------------------
    reset_edge_trig_i : entity work.EDGE_DETECT
    port map (
        CLK             => CLK,
        DI              => reset_raw,
        EDGE            => RST_REQ
    );

    reset_emif_edge_trig_i : entity work.EDGE_DETECT
    port map (
        CLK             => CLK,
        DI              => reset_emif_raw,
        EDGE            => RST_EMIF_REQ
    );

    run_test_edge_trig_i : entity work.EDGE_DETECT
    port map (
        CLK             => CLK,
        DI              => run_test_raw,
        EDGE            => RUN_TEST
    );

    -- Crossing between MI bus and EMIF IP clk domains
    mi_async_i : entity work.MI_ASYNC
    generic map (
        ADDR_WIDTH      => MI_ADDR_WIDTH,
        DATA_WIDTH      => MI_DATA_WIDTH,
        DEVICE          => DEVICE
    )
    port map (
        CLK_M           => MI_CLK,
        RESET_M         => MI_RST,
        MI_M_ADDR       => MI_ADDR,
        MI_M_DWR        => MI_DWR,
        MI_M_BE         => MI_BE,
        MI_M_RD         => MI_RD,
        MI_M_WR         => MI_WR,
        MI_M_ARDY       => MI_ARDY,
        MI_M_DRDY       => MI_DRDY,
        MI_M_DRD        => MI_DRD,

        CLK_S           => CLK,
        RESET_S         => RST,
        MI_S_ADDR       => mi_addr_sync,
        MI_S_DWR        => mi_dwr_sync,
        MI_S_BE         => mi_be_sync,
        MI_S_RD         => mi_rd_sync,
        MI_S_WR         => mi_wr_sync,
        MI_S_ARDY       => mi_ardy_sync,
        MI_S_DRDY       => mi_drdy_sync,
        MI_S_DRD        => mi_drd_sync
    );

    mi_splitter_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map (
        ADDR_WIDTH      => MI_ADDR_WIDTH,
        DATA_WIDTH      => MI_DATA_WIDTH,
        META_WIDTH      => 0,
        PORTS           => MI_PORTS,
        PIPE_TYPE       => "REG",
        ADDR_BASE       => ADDR_BASES,
        ADDR_MASK       => (MI_ADDR_WIDTH - 1 downto 0 => '1'),
        DEVICE          => DEVICE
    )
    port map (
        -- Common interface
        CLK             => CLK,
        RESET           => RST,
        -- Input
        RX_DWR          => mi_dwr_sync,
        RX_MWR          => (others => '0'),
        RX_ADDR         => mi_addr_sync,
        RX_BE           => mi_be_sync,
        RX_RD           => mi_rd_sync,
        RX_WR           => mi_wr_sync,
        RX_ARDY         => mi_ardy_sync,
        RX_DRD          => mi_drd_sync,
        RX_DRDY         => mi_drdy_sync,
        -- Output
        TX_DWR          => mi_splitted_dwr,
        TX_ADDR         => mi_splitted_addr,
        TX_BE           => mi_splitted_be,
        TX_RD           => mi_splitted_rd,
        TX_WR           => mi_splitted_wr,
        TX_ARDY         => mi_splitted_ardy,
        TX_DRD          => mi_splitted_drd,
        TX_DRDY         => mi_splitted_drdy
    );

    ----------------
    -- Wire logic --
    ----------------
    -- Mapping of bits --
    reset_raw                           <= ctrl_in(RST_BIT);
    reset_emif_raw                      <= ctrl_in(RST_EMIF_BIT);
    run_test_raw                        <= ctrl_in(RUN_TEST_BIT);
    MANUAL_EN                           <= ctrl_in(MANUAL_EN_BIT);
    RANDOM_ADDR_EN                      <= ctrl_in(RANDOM_ADDR_EN_BIT);
    ONE_SIMULT_READ                     <= ctrl_in(ONE_SIMULT_READ_BIT);
    AUTO_PRECHARGE                      <= ctrl_in(AUTO_PRECHARGE_BIT);

    ctrl_out(TEST_DONE_BIT)             <= TEST_DONE;
    ctrl_out(TEST_SUCCESS_BIT)          <= TEST_SUCCESS;
    ctrl_out(ECC_ERROR_BIT)             <= ECC_ERROR;
    ctrl_out(CALIB_SUCCESS_BIT)         <= CALIB_SUCCESS;
    ctrl_out(CALIB_FAIL_BIT)            <= CALIB_FAIL;
    ctrl_out(AMM_READY_BIT)             <= AMM_READY;
    -- refresh ovf bits asserted in process bellow
    ctrl_out(MI_DATA_WIDTH - 1 downto AMM_READY_BIT + 1)
                                        <= (others => '0');

    BURST_CNT                           <= burst_cnt_intern(AMM_BURST_COUNT_WIDTH   - 1 downto 0);
    ADDR_LIMIT                          <= addr_lim_intern (AMM_ADDR_WIDTH          - 1 downto 0);
    REFR_PERIOD                         <= refresh_period_intern(REFR_PERIOD_WIDTH  - 1 downto 0);

    -- Base port --
    sel_reg                             <= mi_splitted_addr(MI_BASE_PORT)(MI_ADDR_LIMIT downto MI_ADDR_CUTOFF);
    mi_splitted_ardy(MI_BASE_PORT)      <= mi_splitted_rd(MI_BASE_PORT) or mi_splitted_wr(MI_BASE_PORT);

    -- AMM_GEN port
    AMM_GEN_DWR                         <= mi_splitted_dwr (AMM_GEN_PORT);
    AMM_GEN_ADDR                        <= mi_splitted_addr(AMM_GEN_PORT);
    AMM_GEN_BE                          <= mi_splitted_be  (AMM_GEN_PORT);
    AMM_GEN_RD                          <= mi_splitted_rd  (AMM_GEN_PORT);
    AMM_GEN_WR                          <= mi_splitted_wr  (AMM_GEN_PORT);
    mi_splitted_ardy(AMM_GEN_PORT)      <= AMM_GEN_ARDY;
    mi_splitted_drd (AMM_GEN_PORT)      <= AMM_GEN_DRD;
    mi_splitted_drdy(AMM_GEN_PORT)      <= AMM_GEN_DRDY;

    -- AMM_PROBE port
    AMM_PROBE_DWR                       <= mi_splitted_dwr (AMM_PROBE_PORT);
    AMM_PROBE_ADDR                      <= mi_splitted_addr(AMM_PROBE_PORT);
    AMM_PROBE_BE                        <= mi_splitted_be  (AMM_PROBE_PORT);
    AMM_PROBE_RD                        <= mi_splitted_rd  (AMM_PROBE_PORT);
    AMM_PROBE_WR                        <= mi_splitted_wr  (AMM_PROBE_PORT);
    mi_splitted_ardy(AMM_PROBE_PORT)    <= AMM_PROBE_ARDY;
    mi_splitted_drd (AMM_PROBE_PORT)    <= AMM_PROBE_DRD;
    mi_splitted_drdy(AMM_PROBE_PORT)    <= AMM_PROBE_DRDY;

    ---------------
    -- Registers --
    ---------------
    -- OUT
    mi_out_base_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            case(sel_reg) is
                when CTRL_IN_REG        => mi_splitted_drd(MI_BASE_PORT) <= ctrl_in;
                when CTRL_OUT_REG       => mi_splitted_drd(MI_BASE_PORT) <= ctrl_out;
                when ERR_CNT_REG        => mi_splitted_drd(MI_BASE_PORT) <= err_cnt;
                when BURST_CNT_REG      => mi_splitted_drd(MI_BASE_PORT) <= burst_cnt_intern;
                when ADDR_LIM_REG       => mi_splitted_drd(MI_BASE_PORT) <= addr_lim_intern;
                when REFRESH_TICKS_REG  => mi_splitted_drd(MI_BASE_PORT) <= refresh_period_intern;
                when DEF_REFR_REG       => mi_splitted_drd(MI_BASE_PORT)(REFR_PERIOD_WIDTH - 1 downto 0)
                                                                         <= DEF_REFR_PERIOD;
                when others             => mi_splitted_drd(MI_BASE_PORT) <= X"DEADBEEF";
            end case;
         end if;
    end process;

    -- IN
    mi_in_base_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                ctrl_in                 <= (others => '0');
                burst_cnt_intern        <= std_logic_vector(to_unsigned(DEFAULT_BURST_CNT,  MI_DATA_WIDTH));
                addr_lim_intern         <= std_logic_vector(to_unsigned(DEFAULT_ADDR_LIMIT, MI_DATA_WIDTH));
                refresh_period_intern(REFR_PERIOD_WIDTH - 1 downto 0)
                                        <= DEF_REFR_PERIOD;
            elsif (mi_splitted_wr(MI_BASE_PORT) = '1') then
                case(sel_reg) is
                    when CTRL_IN_REG        => ctrl_in              <= mi_splitted_dwr(MI_BASE_PORT);
                    when BURST_CNT_REG      => burst_cnt_intern     <= mi_splitted_dwr(MI_BASE_PORT);
                    when ADDR_LIM_REG       => addr_lim_intern      <= mi_splitted_dwr(MI_BASE_PORT);
                    when REFRESH_TICKS_REG  => refresh_period_intern<= mi_splitted_dwr(MI_BASE_PORT);
                    when others             =>
                end case;
            end if;
        end if;
    end process;

    -- DRDY
    mi_drdy_base_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            mi_splitted_drdy(MI_BASE_PORT)  <= mi_splitted_rd(MI_BASE_PORT);
        end if;
    end process;

end architecture;
