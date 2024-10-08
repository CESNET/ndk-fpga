-- mem_tester.vhd: Component for testing DDR4 memory
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- .. vhdl:autogenerics:: MEM_TESTER
entity MEM_TESTER is
generic (
    -- Avalon Memory-Mapped (memory interface) data width
    AMM_DATA_WIDTH          : integer := 512;
    AMM_ADDR_WIDTH          : integer := 26;
    AMM_BURST_COUNT_WIDTH   : integer := 7;
    -- Avalon Memory-Mapped (memory interface) frequency in kHz
    AMM_FREQ_KHZ            : integer := 266660;

    -- MI bus data width
    MI_DATA_WIDTH           : integer := 32;
    MI_ADDR_WIDTH           : integer := 32;

    -- Random data generators width
    -- Random data will be made by adding these generators in series
    -- For alowed values se LFSR_SIMPLE_RANDOM_GEN (4, 8, 16, 20, 24, 26, 32, 64)
    RAND_GEN_DATA_WIDTH     : integer := 64;
    -- Width of random generator for addresses (should be equal or larger then AMM_ADDR width)
    RAND_GEN_ADDR_WIDTH     : integer := 26;

    -- Random data generator seed
    RANDOM_DATA_SEED        : slv_array_t(0 to AMM_DATA_WIDTH / RAND_GEN_DATA_WIDTH - 1)(RAND_GEN_DATA_WIDTH - 1 downto 0);
    --RANDOM_ADDR_SEED        : std_logic_vector(RAND_GEN_ADDR_WIDTH - 1 downto 0) := std_logic_vector(resize(to_unsigned(66844679, 32), RAND_GEN_ADDR_WIDTH));
    RANDOM_ADDR_SEED        : std_logic_vector(RAND_GEN_ADDR_WIDTH - 1 downto 0) := resize(X"3FBF807", RAND_GEN_ADDR_WIDTH);


    -- Manual refresh enable
    REFR_REQ_BEFORE_TEST    : boolean := false;
    REFR_PERIOD_WIDTH       : integer := MI_DATA_WIDTH;
    DEF_REFR_PERIOD         : std_logic_vector(REFR_PERIOD_WIDTH - 1 downto 0) := (others => '0');

    -- Enable AMM probe for measurement (depreciated)
    AMM_PROBE_EN            : boolean := false;
    -- Latency histogram precision for AMM probe (depreciated)
    HISTOGRAM_BOXES         : integer := 256;
    -- Default memory burst count
    DEFAULT_BURST_CNT       : integer := 4;
    -- Until which address should be test done (to reduce simulation resources)
    -- Shoud be power of 2
    DEFAULT_ADDR_LIMIT      : integer := 2**AMM_ADDR_WIDTH - 2 ** AMM_BURST_COUNT_WIDTH;
    -- Force random address generator to generate in range 0 to DEFAULT_ADDR_LIMIT (for simulation)
    DEBUG_RAND_ADDR         : boolean := false;
    DEVICE                  : string
);
port(
    -- =======================================================================
    --  Avalon interface from EMIF IP
    -- =======================================================================

    AMM_CLK                 : in std_logic;
    AMM_RST                 : in std_logic;

    -- Indicates when controller is ready
    AMM_READY               : in   std_logic;
    -- When asserted, transaction to current address with current burst count is generated
    AMM_READ                : out  std_logic;
    -- Has to be high for every word in transaction
    AMM_WRITE               : out  std_logic;
    -- Indexed by AMM words (can be set just for the first word of each transaction)
    AMM_ADDRESS             : out  std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
    AMM_READ_DATA           : in   std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    AMM_WRITE_DATA          : out  std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    -- Number of AMM words in one r/w transaction
    AMM_BURST_COUNT         : out  std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    AMM_READ_DATA_VALID     : in   std_logic;

    -- Manual memory refresh period
    REFR_PERIOD             : out std_logic_vector(REFR_PERIOD_WIDTH - 1 downto 0);
    REFR_REQ                : out std_logic;
    REFR_ACK                : in  std_logic := '1';

    -- =======================================================================
    --  Other EMIF IP signals
    -- =======================================================================

    -- Force reset and calibration, must be at least 2 clk at '1'
    EMIF_RST_REQ            : out  std_logic;
    EMIF_RST_DONE           : in   std_logic;
    -- Interrupt to indicate whenever bit error occurred
    EMIF_ECC_ISR            : in   std_logic;
    -- Calibration successful
    EMIF_CAL_SUCCESS        : in   std_logic;
    -- Calibration failed
    EMIF_CAL_FAIL           : in   std_logic;
    -- Auto precharge request
    EMIF_AUTO_PRECHARGE     : out  std_logic;

    -- =======================================================================
    --  MI bus interface
    -- =======================================================================

    MI_CLK                  : in std_logic := '0';
    MI_RST                  : in std_logic := '0';

    MI_DWR                  : in  std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    MI_ADDR                 : in  std_logic_vector(MI_ADDR_WIDTH - 1 downto 0);
    MI_BE                   : in  std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0);
    MI_RD                   : in  std_logic;
    MI_WR                   : in  std_logic;
    MI_ARDY                 : out std_logic;
    MI_DRD                  : out std_logic_vector(MI_DATA_WIDTH - 1 downto 0)          := (others => '0');
    MI_DRDY                 : out std_logic
);
end entity;

-- Notes
-- During random indexing test there will be errors
-- due to ovewriting data on same address
-- Use random indexing test just for latency and speed measurements!

architecture FULL of MEM_TESTER is

    ---------------
    -- Constants --
    ---------------

    type STATES_T is (
        INIT,
        PERFORM_REFRESH,
        DATA_WRITE,
        DATA_READ,
        WRITE_DONE,
        READ_DONE,
        WAITING_READ
    );

    -- AMM MUX --
    -- Indexes depend on mux_sel signal connection!
    constant MUX_SLOT_MAIN          : integer := 0;
    -- Same as MUX_SLOT_MAIN but random addr
    constant MUX_SLOT_RANDOM        : integer := 1;
    constant MUX_SLOT_AMM_GEN       : integer := 2;
    constant MUX_WIDTH              : integer := 3;

    constant EMIF_OUT_WIDTH         : integer := 2;
    constant EMIF_IN_WIDTH          : integer := 4;
    constant EMIF_DELAY             : integer := 1;

    constant ERR_CMP_USE_OUT_REG    : boolean := True;

    -- EMIF user rst request should be at least 2 CLK cycles long
    -- Reset will be hold while mi rst req register bit is set to 1 + this ticks cnt
    constant RST_REQ_TICKS          : integer := 4;
    constant RST_REQ_LIMIT          : std_logic_vector(log2(RST_REQ_TICKS) - 1 downto 0)
        := std_logic_vector(to_unsigned(RST_REQ_TICKS - 1, log2(RST_REQ_TICKS)));

    -- TODO: remove
    constant MI_ADDR_USED_BITS      : integer := 7;
    -- Max address: 0XFF
    constant MI_ADDR_USAGE          : integer := 8;
    constant AMM_GEN_BASE           : std_logic_vector(MI_ADDR_USAGE - 1 downto 0) := X"40";
    constant AMM_PROBE_BASE         : std_logic_vector(MI_ADDR_USAGE - 1 downto 0) := X"60";

    -- AMM_ADDR MUX
    constant SEL_ADDR_CNT           : integer := 2;
    constant SEL_ADDR_WIDTH         : integer := log2(SEL_ADDR_CNT);

    -- AMM MUX config --
    constant MUX_LATENCY            : integer := 1;
    constant SLAVE_INPUT_REG        : boolean := false;
    constant MASTER_OUTPUT_REG      : boolean := false;
    constant MASTER_INPUT_LATENCY   : integer := 1;

    -------------
    -- Signals --
    -------------
    -- Main
    signal amm_rst_delayed          : std_logic;
    signal total_rst                : std_logic;
    signal total_rst_raw            : std_logic;

    -- State machine
    signal curr_state               : STATES_T;
    signal next_state               : STATES_T;

    -- Random gen
    signal random_data              : std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    signal random_en                : std_logic;
    signal random_en_req            : std_logic;
    signal random_rst               : std_logic;

    signal random_addr              : std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
    signal random_addr_raw          : std_logic_vector(RAND_GEN_ADDR_WIDTH - 1 downto 0);
    signal random_addr_en           : std_logic;
    signal random_addr_en_req       : std_logic;
    signal random_addr_rst          : std_logic;

    -- Err cnt
    signal err_found                : std_logic;
    signal read_data_match          : std_logic;
    signal err_rst                  : std_logic;
    signal err_cnt                  : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);

    -- Others
    signal receive_data             : std_logic;
    signal receive_data_delayed     : std_logic;        -- If ERR_CMP_USE_OUT_REG = True
    signal receive_data_delayed_2   : std_logic;        -- If ERR_CMP_USE_OUT_REG = True
    signal wait_for_read_data       : std_logic;

    -- AMM R/W
    -- AMM R/W delayed (because manual buff BRAM is delayed by 1 clk)
    signal amm_write_delayed        : std_logic;

    -- Memory address for r/w request
    signal curr_address             : std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
    signal addr_incr                : std_logic;
    signal addr_incr_req_wr         : std_logic;    -- Address incr only when burst is done
    signal addr_incr_req_rd         : std_logic;    -- Does not depend on burst done
    signal addr_lim_reached         : std_logic;

    -- Memory address for receiving data
    -- (readed data can be received while read requests are beeing generated)
    signal curr_read_address        : std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
    signal read_addr_incr           : std_logic;
    signal read_addr_lim_reached    : std_logic;

    -- Burst for writing (indexed from 1 to match mi_burst_cnt)
    signal curr_burst_cnt           : std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    signal burst_done               : std_logic;
    signal burst_en                 : std_logic;

    -- Burst for reading (indexed from 1 to match mi_burst_cnt)
    signal curr_read_burst_cnt      : std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    signal read_burst_done          : std_logic;
    signal read_burst_en            : std_logic;

    -- Signals for keeping emif_rst_req at '1' for RST_REQ_TICK_CNT
    signal curr_rst_req_ticks       : std_logic_vector(log2(RST_REQ_TICKS) - 1 downto 0);
    signal rst_req_en               : std_logic;
    signal rst_req_done             : std_logic;

    -- Test related
    signal run_test                 : std_logic;
    signal test_done                : std_logic;
    signal set_test_done            : std_logic;
    signal test_success             : std_logic;
    signal addr_limit               : std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);

    signal read_running             : std_logic;
    -- 1 when only 1 simult read is disabled or when on other transaction is running
    signal simult_en_read           : std_logic;

    -- AMM bus mux --
    signal mux_sel                  : std_logic_vector(log2(MUX_WIDTH) - 1 downto 0);

    signal amm_muxed_ready           : std_logic_vector(MUX_WIDTH - 1 downto 0);
    signal amm_muxed_read            : std_logic_vector(MUX_WIDTH - 1 downto 0);
    signal amm_muxed_write           : std_logic_vector(MUX_WIDTH - 1 downto 0);
    signal amm_muxed_read_data_valid : std_logic_vector(MUX_WIDTH - 1 downto 0);
    signal amm_muxed_address         : slv_array_t(MUX_WIDTH - 1 downto 0)(AMM_ADDR_WIDTH - 1 downto 0);
    signal amm_muxed_read_data       : slv_array_t(MUX_WIDTH - 1 downto 0)(AMM_DATA_WIDTH - 1 downto 0);
    signal amm_muxed_write_data      : slv_array_t(MUX_WIDTH - 1 downto 0)(AMM_DATA_WIDTH - 1 downto 0);
    signal amm_muxed_burst_count     : slv_array_t(MUX_WIDTH - 1 downto 0)(AMM_BURST_COUNT_WIDTH - 1 downto 0);

    signal amm_intern_ready         : std_logic;
    signal amm_intern_read          : std_logic;
    signal amm_intern_write         : std_logic;
    signal amm_intern_read_data     : std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    signal amm_intern_write_data    : std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    signal amm_intern_burst_count   : std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    signal amm_intern_read_data_valid : std_logic;

    signal emif_intern_rst_req      : std_logic;
    signal emif_intern_rst_done     : std_logic;
    signal emif_intern_ecc_isr      : std_logic;
    signal emif_intern_cal_success  : std_logic;
    signal emif_intern_cal_fail     : std_logic;
    signal emif_intern_precharge    : std_logic;

    signal emif_out_piped           : slv_array_t(0 to EMIF_DELAY)(EMIF_OUT_WIDTH - 1 downto 0);
    signal emif_out                 : std_logic_vector(EMIF_OUT_WIDTH - 1 downto 0);
    signal emif_in_piped            : slv_array_t(0 to EMIF_DELAY)(EMIF_IN_WIDTH - 1 downto 0);
    signal emif_in                  : std_logic_vector(EMIF_IN_WIDTH - 1 downto 0);

    -- MI bus --
    signal mi_addr_cutted           : std_logic_vector(MI_ADDR_USAGE - 1 downto 0);
    -- in
    signal mi_rst_req               : std_logic;
    signal mi_rst_emif_req          : std_logic;
    signal mi_run_test              : std_logic;
    signal mi_manual_en             : std_logic;
    signal mi_random_addr_en        : std_logic;
    signal mi_one_simult_read       : std_logic;
    signal mi_auto_precharge        : std_logic;

    -- out
    signal mi_test_done             : std_logic;
    signal mi_test_success          : std_logic;
    signal mi_ecc_error             : std_logic;
    signal mi_calib_success         : std_logic;
    signal mi_calib_fail            : std_logic;

    signal mi_err_cnt               : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal mi_burst_cnt             : std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    signal mi_refresh_period        : std_logic_vector(REFR_PERIOD_WIDTH - 1 downto 0);
    signal mi_refresh_ticks_ovf     : std_logic;
    signal mi_refresh_counters_ovf  : std_logic;
    signal mi_refresh_sum_ovf       : std_logic;

    -- AMM_GEN --
    signal amm_gen_dwr              : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal amm_gen_addr             : std_logic_vector(MI_ADDR_USAGE - 1 downto 0);
    signal amm_gen_be               : std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0);
    signal amm_gen_rd               : std_logic;
    signal amm_gen_wr               : std_logic;
    signal amm_gen_ardy             : std_logic;
    signal amm_gen_drd              : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal amm_gen_drdy             : std_logic;

    -- AMM PROBE --
    signal amm_probe_dwr            : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal amm_probe_addr           : std_logic_vector(MI_ADDR_USAGE - 1 downto 0);
    signal amm_probe_be             : std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0);
    signal amm_probe_rd             : std_logic;
    signal amm_probe_wr             : std_logic;
    signal amm_probe_ardy           : std_logic;
    signal amm_probe_drd            : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal amm_probe_drdy           : std_logic;

    -- RANDOM gen --
    component LFSR_SIMPLE_RANDOM_GEN is
        generic(
           DATA_WIDTH : natural := RAND_GEN_DATA_WIDTH;
           -- Reset seed value, all bits must NOT be set high!!!
           RESET_SEED : std_logic_vector(DATA_WIDTH-1 downto 0)
        );
        port(
           CLK    : in  std_logic;
           RESET  : in  std_logic;
           ENABLE : in  std_logic;
           DATA   : out std_logic_vector(DATA_WIDTH-1 downto 0)
        );
     end component;

begin
    ----------------
    -- Components --
    ----------------

    -- Generation of multiple random genenerators in series to match AMM_DATA width
    random_generator_g : for i in 0 to (AMM_DATA_WIDTH / RAND_GEN_DATA_WIDTH - 1) generate
        random_gen_i : LFSR_SIMPLE_RANDOM_GEN
        generic map(
            DATA_WIDTH          => RAND_GEN_DATA_WIDTH,
            RESET_SEED          => RANDOM_DATA_SEED(i)
        )
        port map(
            CLK                 => AMM_CLK,
            RESET               => random_rst,
            ENABLE              => random_en,
            DATA                => random_data(RAND_GEN_DATA_WIDTH * (i + 1) - 1 downto RAND_GEN_DATA_WIDTH * i)
        );
    end generate;

    -- Generation of the random address
    random_addr_gen_i : LFSR_SIMPLE_RANDOM_GEN
        generic map(
            DATA_WIDTH          => RAND_GEN_ADDR_WIDTH,
            RESET_SEED          => RANDOM_ADDR_SEED
        )
        port map(
            CLK                 => AMM_CLK,
            RESET               => random_addr_rst,
            ENABLE              => random_addr_en,
            DATA                => random_addr_raw
        );

    read_data_cmp_i : entity work.GEN_CMP
    generic map (
        DATA_WIDTH              => AMM_DATA_WIDTH,
        IS_DSP                  => false,
        REG_IN                  => ERR_CMP_USE_OUT_REG,
        REG_OUT                 => ERR_CMP_USE_OUT_REG,
        COMPARE_EQ              => true ,
        COMPARE_CMP             => false
    )
    port map (
        CLK                     => AMM_CLK,
        RESET                   => total_rst,
        A                       => amm_intern_read_data,
        B                       => random_data,
        EQ                      => read_data_match
    );

    amm_mux_i : entity work.AMM_MUX
    generic map (
        MUX_WIDTH               => MUX_WIDTH,
        MUX_LATENCY             => MUX_LATENCY,
        SLAVE_INPUT_REG         => SLAVE_INPUT_REG,
        MASTER_OUTPUT_REG       => MASTER_OUTPUT_REG,
        MASTER_INPUT_LATENCY    => MASTER_INPUT_LATENCY,

        AMM_DATA_WIDTH          => AMM_DATA_WIDTH,
        AMM_ADDR_WIDTH          => AMM_ADDR_WIDTH,
        AMM_BURST_COUNT_WIDTH   => AMM_BURST_COUNT_WIDTH
    )
    port map (
        AMM_CLK                     => AMM_CLK,
        AMM_RST                     => AMM_RST,
        MUX_SEL                     => mux_sel,

        MASTER_AMM_READY            => AMM_READY,
        MASTER_AMM_READ             => AMM_READ,
        MASTER_AMM_WRITE            => AMM_WRITE,
        MASTER_AMM_READ_DATA_VALID  => AMM_READ_DATA_VALID,
        MASTER_AMM_ADDRESS          => AMM_ADDRESS,
        MASTER_AMM_READ_DATA        => AMM_READ_DATA,
        MASTER_AMM_WRITE_DATA       => AMM_WRITE_DATA,
        MASTER_AMM_BURST_COUNT      => AMM_BURST_COUNT,

        SLAVE_AMM_READY             => amm_muxed_ready,
        SLAVE_AMM_READ              => amm_muxed_read,
        SLAVE_AMM_WRITE             => amm_muxed_write,
        SLAVE_AMM_READ_DATA_VALID   => amm_muxed_read_data_valid,
        SLAVE_AMM_ADDRESS           => amm_muxed_address,
        SLAVE_AMM_READ_DATA         => amm_muxed_read_data,
        SLAVE_AMM_WRITE_DATA        => amm_muxed_write_data,
        SLAVE_AMM_BURST_COUNT       => amm_muxed_burst_count
    );

    mem_tester_mi_i : entity work.MEM_TESTER_MI
    generic map (
        MI_DATA_WIDTH           => MI_DATA_WIDTH,
        MI_ADDR_WIDTH           => MI_ADDR_USAGE,
        AMM_ADDR_WIDTH          => AMM_ADDR_WIDTH,
        AMM_BURST_COUNT_WIDTH   => AMM_BURST_COUNT_WIDTH,
        REFR_PERIOD_WIDTH       => REFR_PERIOD_WIDTH,

        AMM_GEN_BASE            => AMM_GEN_BASE,
        AMM_PROBE_BASE          => AMM_PROBE_BASE,
        DEFAULT_BURST_CNT       => DEFAULT_BURST_CNT,
        DEFAULT_ADDR_LIMIT      => DEFAULT_ADDR_LIMIT,
        DEF_REFR_PERIOD         => DEF_REFR_PERIOD,

        DEVICE                  => DEVICE
    )
    port map(
        -- MI master --
        MI_CLK                  => MI_CLK,
        MI_RST                  => MI_RST,

        MI_DWR                  => MI_DWR,
        MI_ADDR                 => mi_addr_cutted,
        MI_BE                   => MI_BE,
        MI_RD                   => MI_RD,
        MI_WR                   => MI_WR,
        MI_ARDY                 => MI_ARDY,

        MI_DRD                  => MI_DRD,
        MI_DRDY                 => MI_DRDY,

        CLK                     => AMM_CLK,
        RST                     => amm_rst_delayed,

        -- Master => slave
        RST_REQ                 => mi_rst_req,
        RST_EMIF_REQ            => mi_rst_emif_req,
        RUN_TEST                => mi_run_test,
        MANUAL_EN               => mi_manual_en,
        RANDOM_ADDR_EN          => mi_random_addr_en,
        ONE_SIMULT_READ         => mi_one_simult_read,
        AUTO_PRECHARGE          => mi_auto_precharge,
        BURST_CNT               => mi_burst_cnt,
        ADDR_LIMIT              => addr_limit,
        REFR_PERIOD             => REFR_PERIOD,

        -- Slave => master
        TEST_DONE               => mi_test_done,
        TEST_SUCCESS            => mi_test_success,
        ECC_ERROR               => mi_ecc_error,
        CALIB_SUCCESS           => mi_calib_success,
        CALIB_FAIL              => mi_calib_fail,
        AMM_READY               => AMM_READY,
        ERR_CNT                 => mi_err_cnt,

        AMM_GEN_DWR             => amm_gen_dwr,
        AMM_GEN_ADDR            => amm_gen_addr,
        AMM_GEN_BE              => amm_gen_be,
        AMM_GEN_RD              => amm_gen_rd,
        AMM_GEN_WR              => amm_gen_wr,
        AMM_GEN_ARDY            => amm_gen_ardy,
        AMM_GEN_DRD             => amm_gen_drd,
        AMM_GEN_DRDY            => amm_gen_drdy,

        AMM_PROBE_DWR           => amm_probe_dwr,
        AMM_PROBE_ADDR          => amm_probe_addr,
        AMM_PROBE_BE            => amm_probe_be,
        AMM_PROBE_RD            => amm_probe_rd,
        AMM_PROBE_WR            => amm_probe_wr,
        AMM_PROBE_ARDY          => amm_probe_ardy,
        AMM_PROBE_DRD           => amm_probe_drd,
        AMM_PROBE_DRDY          => amm_probe_drdy
    );

    amm_gen_i : entity work.AMM_GEN
    generic map (
        MI_DATA_WIDTH           => MI_DATA_WIDTH,
        MI_ADDR_WIDTH           => MI_ADDR_USAGE,

        AMM_DATA_WIDTH          => AMM_DATA_WIDTH,
        AMM_ADDR_WIDTH          => AMM_ADDR_WIDTH,
        AMM_BURST_COUNT_WIDTH   => AMM_BURST_COUNT_WIDTH,

        MI_ADDR_BASE            => AMM_GEN_BASE,
        MI_ADDR_USED_BITS       => MI_ADDR_USED_BITS,
        DEVICE                  => DEVICE
    )
    port map (
        CLK                     => AMM_CLK,
        RST                     => total_rst,

        MI_DWR                  => amm_gen_dwr,
        MI_ADDR                 => amm_gen_addr,
        MI_BE                   => amm_gen_be,
        MI_RD                   => amm_gen_rd,
        MI_WR                   => amm_gen_wr,
        MI_ARDY                 => amm_gen_ardy,
        MI_DRD                  => amm_gen_drd,
        MI_DRDY                 => amm_gen_drdy,

        AMM_READY               => amm_muxed_ready(MUX_SLOT_AMM_GEN),
        AMM_READ                => amm_muxed_read(MUX_SLOT_AMM_GEN),
        AMM_WRITE               => amm_muxed_write(MUX_SLOT_AMM_GEN),
        AMM_ADDRESS             => amm_muxed_address(MUX_SLOT_AMM_GEN),
        AMM_READ_DATA           => amm_muxed_read_data(MUX_SLOT_AMM_GEN),
        AMM_WRITE_DATA          => amm_muxed_write_data(MUX_SLOT_AMM_GEN),
        AMM_BURST_COUNT         => amm_muxed_burst_count(MUX_SLOT_AMM_GEN),
        AMM_READ_DATA_VALID     => amm_muxed_read_data_valid(MUX_SLOT_AMM_GEN)
    );

    amm_probe_g : if (AMM_PROBE_EN) generate
        amm_probe_i : entity work.AMM_PROBE
        generic map (
            MI_DATA_WIDTH           => MI_DATA_WIDTH,
            MI_ADDR_WIDTH           => MI_ADDR_USAGE,

            AMM_DATA_WIDTH          => AMM_DATA_WIDTH,
            AMM_ADDR_WIDTH          => AMM_ADDR_WIDTH,
            AMM_BURST_COUNT_WIDTH   => AMM_BURST_COUNT_WIDTH,
            AMM_FREQ_KHZ            => AMM_FREQ_KHZ,

            MI_ADDR_BASE            => AMM_PROBE_BASE,
            MI_ADDR_USED_BITS       => MI_ADDR_USED_BITS,
            HISTOGRAM_BOXES         => HISTOGRAM_BOXES,
            DEVICE                  => DEVICE
        )
        port map (
            CLK                     => AMM_CLK,
            RST                     => total_rst,

            MI_DWR                  => amm_probe_dwr ,
            MI_ADDR                 => amm_probe_addr,
            MI_BE                   => amm_probe_be  ,
            MI_RD                   => amm_probe_rd  ,
            MI_WR                   => amm_probe_wr  ,
            MI_ARDY                 => amm_probe_ardy,
            MI_DRD                  => amm_probe_drd ,
            MI_DRDY                 => amm_probe_drdy,

            AMM_READY               => AMM_READY          ,
            AMM_READ                => AMM_READ           ,
            AMM_WRITE               => AMM_WRITE          ,
            AMM_ADDRESS             => AMM_ADDRESS        ,
            AMM_READ_DATA           => AMM_READ_DATA      ,
            AMM_WRITE_DATA          => AMM_WRITE_DATA     ,
            AMM_BURST_COUNT         => AMM_BURST_COUNT    ,
            AMM_READ_DATA_VALID     => AMM_READ_DATA_VALID
        );
    end generate;
    no_amm_probe_g : if (AMM_PROBE_EN = false) generate
        amm_probe_ardy      <= '1';
        amm_probe_drd       <= X"DEAD_BEAF";
        amm_probe_drdy      <= amm_probe_rd;
    end generate;

    ------------------------
    -- Interconnect logic --
    ------------------------

    -- Avalon interface mux --
    amm_intern_ready           <= amm_muxed_ready          (MUX_SLOT_MAIN) or
                                  amm_muxed_ready          (MUX_SLOT_RANDOM);
    amm_intern_read_data_valid <= amm_muxed_read_data_valid(MUX_SLOT_MAIN) or
                                  amm_muxed_read_data_valid(MUX_SLOT_RANDOM);
    amm_intern_read_data       <= amm_muxed_read_data      (MUX_SLOT_MAIN);
    amm_muxed_read       (MUX_SLOT_MAIN) <= amm_intern_read       ;
    amm_muxed_write      (MUX_SLOT_MAIN) <= amm_intern_write      ;
    amm_muxed_write_data (MUX_SLOT_MAIN) <= amm_intern_write_data ;
    amm_muxed_burst_count(MUX_SLOT_MAIN) <= amm_intern_burst_count;
    amm_muxed_address    (MUX_SLOT_MAIN) <= curr_address          ;

    amm_muxed_read       (MUX_SLOT_RANDOM) <= amm_intern_read       ;
    amm_muxed_write      (MUX_SLOT_RANDOM) <= amm_intern_write      ;
    amm_muxed_write_data (MUX_SLOT_RANDOM) <= amm_intern_write_data ;
    amm_muxed_burst_count(MUX_SLOT_RANDOM) <= amm_intern_burst_count;
    amm_muxed_address    (MUX_SLOT_RANDOM) <= random_addr           ;

    mux_sel <=
        std_logic_vector(to_unsigned(MUX_SLOT_MAIN, mux_sel'length)) when (mi_manual_en = '0' and mi_random_addr_en = '0') else
        std_logic_vector(to_unsigned(MUX_SLOT_RANDOM, mux_sel'length)) when (mi_manual_en = '0' and mi_random_addr_en = '1') else
        std_logic_vector(to_unsigned(MUX_SLOT_AMM_GEN, mux_sel'length));

    -- AMM bus intern --
    amm_intern_burst_count      <= mi_burst_cnt;
    amm_intern_write_data       <= random_data;

    -- Other EMIF signals --
    (emif_intern_rst_done, emif_intern_ecc_isr, emif_intern_cal_success, emif_intern_cal_fail)
                                <= emif_in_piped(EMIF_DELAY);
    emif_in_piped(0)            <= (EMIF_RST_DONE, EMIF_ECC_ISR, EMIF_CAL_SUCCESS, EMIF_CAL_FAIL);

    emif_out_piped(0)(0)        <= emif_intern_rst_req;
    emif_out_piped(0)(1)        <= mi_auto_precharge;
    EMIF_RST_REQ                <= emif_out_piped(EMIF_DELAY)(0);
    EMIF_AUTO_PRECHARGE         <= emif_out_piped(EMIF_DELAY)(1);

    -- Test related signals --
    receive_data                <= amm_intern_read_data_valid and wait_for_read_data and (not mi_manual_en);

    err_found_cmp_reg_g : if (ERR_CMP_USE_OUT_REG = True) generate
        err_found               <= (not read_data_match) and receive_data_delayed_2;
    end generate;
    err_found_cmp_no_reg_g : if (ERR_CMP_USE_OUT_REG = False) generate
        err_found               <= (not read_data_match) and receive_data;
    end generate;

    test_success                <= '1' when (err_cnt = std_logic_vector(to_unsigned(0, err_cnt'length))) else
                                   '0';

    -- Enable signals --
    random_en                   <= random_en_req or receive_data;
    random_addr_en              <= random_addr_en_req and addr_incr;
    read_burst_en               <= receive_data;
    simult_en_read              <= (not mi_one_simult_read) or (not read_running);
    addr_incr                   <= (burst_done and addr_incr_req_wr) or (addr_incr_req_rd and amm_intern_ready and simult_en_read);
    read_addr_incr              <= receive_data and read_burst_done;

    -- Counters limits --
    addr_lim_reached            <= '1' when (curr_address = addr_limit and amm_intern_ready = '1' and simult_en_read = '1') else
                                   '0';
    read_addr_lim_reached       <= '1' when (curr_read_address = addr_limit and amm_intern_read_data_valid = '1') else
                                   '0';
    burst_done                  <= '1' when (curr_burst_cnt = mi_burst_cnt and amm_intern_ready = '1') else
                                   '0';
    read_burst_done             <= '1' when (curr_read_burst_cnt = mi_burst_cnt and amm_intern_read_data_valid = '1') else
                                   '0';

    -- Reset logic --
    total_rst_raw               <= mi_rst_req or amm_rst_delayed;

    -- Other signals --
    rst_req_done                <= '1' when (curr_rst_req_ticks = RST_REQ_LIMIT) else
                                   '0';

    -- MI signals --
    mi_addr_cutted              <= MI_ADDR(MI_ADDR_USAGE - 1 downto 0);
    run_test                    <= mi_run_test;

    -- out
    mi_test_done                <= test_done;
    mi_test_success             <= test_success;
    mi_calib_success            <= emif_intern_cal_success;
    mi_calib_fail               <= emif_intern_cal_fail;
    mi_err_cnt                  <= err_cnt;

    random_addr_no_debug_g : if (DEBUG_RAND_ADDR = False) generate
        random_addr             <= random_addr_raw(AMM_ADDR_WIDTH - 1 downto 0);
    end generate;
    random_addr_debug_g    : if (DEBUG_RAND_ADDR = True) generate
        random_addr(log2(DEFAULT_ADDR_LIMIT) - 2 downto 0)
                                <= random_addr_raw(log2(DEFAULT_ADDR_LIMIT) - 2 downto 0);
        random_addr(AMM_ADDR_WIDTH - 1 downto log2(DEFAULT_ADDR_LIMIT) - 1)
                                <= (others => '0');
    end generate;

    ---------------
    -- Registers --
    ---------------

    -- Addr counters --
    curr_address_reg_p : process (AMM_CLK)
    begin
         if (rising_edge(AMM_CLK)) then
            if (total_rst = '1' or (addr_lim_reached = '1' and addr_incr = '1')) then
                curr_address <= (others => '0');
            else
                if (addr_incr = '1') then
                    curr_address <= std_logic_vector(unsigned(curr_address) + unsigned(mi_burst_cnt));
                end if;
            end if;
        end if;
    end process;

    curr_read_address_reg_p : process (AMM_CLK)
    begin
         if (rising_edge(AMM_CLK)) then
            if (total_rst = '1' or (read_addr_lim_reached = '1' and read_addr_incr = '1')) then
                curr_read_address <= (others => '0');
            else
                if (read_addr_incr = '1') then
                    curr_read_address <= std_logic_vector(unsigned(curr_read_address) + unsigned(mi_burst_cnt));
                end if;
            end if;
        end if;
    end process;

    -- Err counter --
    err_cnt_p : process (AMM_CLK)
    begin
         if (rising_edge(AMM_CLK)) then
            if (total_rst = '1' or err_rst = '1') then
                err_cnt <= (others => '0');
            else
                if (err_found = '1') then
                    err_cnt <= std_logic_vector(unsigned(err_cnt) + 1);
                end if;
            end if;
        end if;
    end process;

    -- Burst counters --
    burst_p : process(AMM_CLK)
    begin
        if (rising_edge(AMM_CLK)) then
            if (total_rst = '1' or (burst_done = '1' and burst_en = '1')) then
                curr_burst_cnt <= std_logic_vector(to_unsigned(1, AMM_BURST_COUNT_WIDTH));
            elsif (burst_en = '1') then
                curr_burst_cnt <= std_logic_vector(unsigned(curr_burst_cnt) + 1);
            end if;
        end if;
    end process;

    read_burst_p : process(AMM_CLK)
    begin
        if (rising_edge(AMM_CLK)) then
            if (total_rst = '1' or (read_burst_done = '1' and read_burst_en = '1')) then
                curr_read_burst_cnt <= std_logic_vector(to_unsigned(1, AMM_BURST_COUNT_WIDTH));
            elsif (read_burst_en = '1') then
                curr_read_burst_cnt <= std_logic_vector(unsigned(curr_read_burst_cnt) + 1);
            end if;
        end if;
    end process;

    -- Reset request for EMIF IP --
    rst_req_tick_p : process(AMM_CLK)
    begin
        if (rising_edge(AMM_CLK)) then
            if (total_rst = '1' or rst_req_done = '1') then
                curr_rst_req_ticks <= (others => '0');
            elsif(rst_req_en = '1') then
                curr_rst_req_ticks <= std_logic_vector(unsigned(curr_rst_req_ticks) + 1);
            end if;
        end if;
    end process;

    rst_req_en_p : process(AMM_CLK)
    begin
        if (rising_edge(AMM_CLK)) then
            if (amm_rst_delayed = '1') then
                rst_req_en <= '0';
                emif_intern_rst_req <= '0';
            elsif (mi_rst_emif_req = '1') then
                rst_req_en <= '1';
                emif_intern_rst_req <= '1';
            elsif(rst_req_done = '1') then
                rst_req_en <= '0';
                emif_intern_rst_req <= '0';
            end if;
        end if;
    end process;

    -- Test done proc (to hold test done state) --
    test_done_p : process(AMM_CLK)
    begin
        if (rising_edge(AMM_CLK)) then
            if (total_rst = '1') then
                test_done   <= '0';
            elsif(set_test_done = '1') then
                test_done   <= '1';
            end if;
        end if;
    end process;

    total_rst_p : process(AMM_CLK)
    begin
        if (rising_edge(AMM_CLK)) then
            total_rst   <= total_rst_raw;
        end if;
    end process;

    emif_out_piped_g : for i in 0 to EMIF_DELAY - 1 generate
        emif_out_piped_p : process(AMM_CLK)
        begin
            if (rising_edge(AMM_CLK)) then
                emif_out_piped(i + 1) <= emif_out_piped(i);
            end if;
        end process;
    end generate;

    emif_in_piped_g : for i in 0 to EMIF_DELAY - 1 generate
        emif_in_piped_p : process(AMM_CLK)
        begin
            if (rising_edge(AMM_CLK)) then
                emif_in_piped(i + 1) <= emif_in_piped(i);
            end if;
        end process;
    end generate;

    -- MI signals --
    ecc_err_p : process(AMM_CLK)
    begin
        if (rising_edge(AMM_CLK)) then
            if (total_rst = '1') then
                mi_ecc_error     <= '0';
            elsif(emif_intern_ecc_isr = '1') then
                mi_ecc_error    <= '1';
            end if;
        end if;
    end process;

    -- AMM read / write delayed
    amm_write_delayed_p : process(AMM_CLK)
    begin
        if (rising_edge(AMM_CLK)) then
            if (total_rst = '1') then
                amm_write_delayed <= '0';
            else
                amm_write_delayed  <= amm_intern_write;
            end if;
        end if;
    end process;

    -- receive_data delayed
    receive_data_delayed_p : process(AMM_CLK)
    begin
        if (rising_edge(AMM_CLK)) then
            if (total_rst = '1') then
                receive_data_delayed    <= '0';
                receive_data_delayed_2  <= '0';
            else
                receive_data_delayed    <= receive_data;
                receive_data_delayed_2  <= receive_data_delayed;
            end if;
        end if;
    end process;

    amm_rst_delayed_p : process(AMM_CLK)
    begin
        if (rising_edge(AMM_CLK)) then
            amm_rst_delayed <= AMM_RST;
        end if;
    end process;

    -- Not usable for more then 1 simultaneous read request
    read_running_p : process(AMM_CLK)
    begin
        if (rising_edge(AMM_CLK)) then
            if (total_rst = '1') then
                read_running    <= '0';
            else
                if (amm_intern_read = '1') then
                    read_running <= '1';
                elsif (amm_intern_read_data_valid = '1' and read_burst_done = '1') then
                    read_running <= '0';
                end if;
            end if;
        end if;
    end process;

    -------------------
    -- STATE MACHINE --
    -------------------

    -- next state logic
    state_reg_p : process (AMM_CLK)
    begin
        if (rising_edge(AMM_CLK)) then
            if (total_rst = '1') then
                curr_state <= INIT;
            else
                curr_state <= next_state;
            end if;
        end if;
    end process;

    -- output logic
    process (all)
    begin
        amm_intern_read     <= '0';
        amm_intern_write    <= '0';

        addr_incr_req_wr    <= '0';
        addr_incr_req_rd    <= '0';

        random_en_req       <= '0';
        random_rst          <= '0';
        random_addr_en_req  <= '0';
        random_addr_rst     <= '0';

        burst_en            <= '0';
        err_rst             <= '0';

        wait_for_read_data  <= '0';
        set_test_done       <= '0';

        REFR_REQ            <= '0';

        case curr_state is

            when INIT =>
                random_rst              <= '1';
                random_addr_rst         <= '1';
                if (rst_req_en = '0' and run_test = '1') then
                    err_rst             <= '1';
                end if;

                if (rst_req_en = '0' and mi_manual_en = '0' and run_test = '1') then
                    REFR_REQ            <= '1';
                end if;

            when PERFORM_REFRESH =>

            when DATA_WRITE =>
                if (amm_intern_ready = '1') then
                    amm_intern_write    <= '1';
                    addr_incr_req_wr    <= '1';
                    burst_en            <= '1';
                    random_en_req       <= '1';

                    if (mi_random_addr_en = '1') then
                        random_addr_en_req <= '1';
                    end if;
                end if;

            when DATA_READ =>
                wait_for_read_data      <= '1';
                addr_incr_req_rd        <= '1';
                random_addr_en_req      <= '1';

                if (amm_intern_ready = '1' and simult_en_read = '1') then
                    amm_intern_read     <= '1';
                end if;

            when WAITING_READ =>
                -- Wait for the remaining requests
                wait_for_read_data      <= '1';

            when WRITE_DONE =>
                random_rst              <= '1';
                random_addr_rst         <= '1';

            when READ_DONE =>
                set_test_done           <= '1';

            when others =>
                null;

        end case;
    end process;

    -- next state logic
    process (all)
    begin
        next_state <= curr_state;

        case curr_state is

            when INIT =>
                if (rst_req_en = '0' and mi_manual_en = '0') then
                    if (run_test = '1') then
                        if (REFR_REQ_BEFORE_TEST = true) then
                            next_state      <= PERFORM_REFRESH;
                        else
                            next_state      <= DATA_WRITE;
                        end if;
                    end if;
                end if;

            when PERFORM_REFRESH =>
                if (REFR_ACK = '1') then
                    next_state      <= DATA_WRITE;
                end if;

            when DATA_WRITE =>
                -- Last write request
                if (addr_lim_reached = '1' and burst_done = '1') then
                    next_state      <= WRITE_DONE;
                end if;

            when DATA_READ =>
                if (addr_lim_reached = '1') then
                    next_state      <= WAITING_READ;
                end if;

            when WAITING_READ =>
                if (read_addr_lim_reached = '1')  then
                    next_state      <= READ_DONE;
                end if;

            when WRITE_DONE =>
                next_state          <= DATA_READ;

            when READ_DONE =>
                next_state          <= INIT;

            when others => null;

        end case;
    end process;

end architecture;
