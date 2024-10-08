-- testbench.vhd: Testbench for simulation of mem_tester component
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.mi_sim_pkg.all;
use work.math_pack.all;
use work.type_pack.all;


entity TESTBENCH is
end entity;

architecture BEHAVIORAL Of TESTBENCH is
    constant DEVICE                 : string := "STRATIX10";

    constant AMM_DATA_WIDTH         : integer := 576;   --512;
    constant AMM_ADDR_WIDTH         : integer := 26;
    constant AMM_BURST_COUNT_WIDTH  : integer := 7;

    constant MI_DATA_WIDTH          : integer := 32;
    constant MI_ADDR_WIDTH          : integer := 32;

    constant AMM_CLK_PERIOD         : time := 4 ns;     -- 266.66 MHz
    constant MI_CLK_PERIOD          : time := 10 ns;    -- 100 MHz

    constant AMM_RST_INIT_TIME      : time := 40 ns;
    constant MI_RST_INIT_TIME       : time := 40 ns;

    constant DEFAULT_BURST_CNT      : integer  := 4;
    -- Used as max memory size for simulation
    constant ADDR_LIMIT             : integer  := DEFAULT_BURST_CNT * 128;
    constant MEM_SIZE               : integer  := ADDR_LIMIT + 2 ** AMM_BURST_COUNT_WIDTH;

    ------------
    -- MI bus --
    ------------
    -- Comp address bases
    constant AMM_GEN_BASE           : integer := 64;
    constant AMM_PROBE_BASE         : integer := 96;

    -- Register addresses
    constant MI_CTRL_IN_ADDR        : integer := 0;
    constant MI_CTRL_OUT_ADDR       : integer := 4;
    constant MI_ERR_CNT_ADDR        : integer := 8;
    constant MI_BURST_CNT_ADDR      : integer := 12;
    constant MI_ADDR_LIM_ADDR       : integer := 16;
    constant MI_REFRESH_PERIOD_ADDR : integer := 20;

    constant AMM_GEN_CTRL_ADDR      : integer := AMM_GEN_BASE;
    constant AMM_GEN_ADDR_ADDR      : integer := AMM_GEN_BASE + 4;
    constant AMM_GEN_SLICE_ADDR     : integer := AMM_GEN_BASE + 8;
    constant AMM_GEN_DATA_ADDR      : integer := AMM_GEN_BASE + 12;
    constant AMM_GEN_BURST_ADDR     : integer := AMM_GEN_BASE + 16;

    constant AMM_PROB_CTRL_ADDR     : integer := AMM_PROBE_BASE;
    constant AMM_PROB_WR_TICKS_ADDR : integer := AMM_PROBE_BASE + 4;
    constant AMM_PROB_RD_TICKS_ADDR : integer := AMM_PROBE_BASE + 8;
    constant AMM_PROB_RW_TICKS_ADDR : integer := AMM_PROBE_BASE + 12;
    constant AMM_PROB_WR_WORDS_ADDR : integer := AMM_PROBE_BASE + 16;
    constant AMM_PROB_RD_WORDS_ADDR : integer := AMM_PROBE_BASE + 20;
    constant AMM_PROB_REQ_WORDS_ADDR      : integer := AMM_PROBE_BASE + 24;
    constant AMM_PROB_LATENCY_SUM_1_ADDR    : integer := AMM_PROBE_BASE + 28;
    constant AMM_PROB_LATENCY_SUM_2_ADDR    : integer := AMM_PROBE_BASE + 32;
    constant AMM_PROB_LATENCY_MIN_ADDR    : integer := AMM_PROBE_BASE + 36;
    constant AMM_PROB_LATENCY_MAX_ADDR    : integer := AMM_PROBE_BASE + 40;
    constant AMM_PROB_HIST_CNT     : integer := AMM_PROBE_BASE + 44;
    constant AMM_PROB_HIST_SEL     : integer := AMM_PROBE_BASE + 48;

    -- Bits in registers
    -- CORE
    -- CTRL IN REG
    constant MI_RST_BIT             : integer := 0;
    constant MI_RST_EMIF_BIT        : integer := 1;
    constant MI_RUN_TEST_BIT        : integer := 2;
    constant MI_MANUAL_EN_BIT       : integer := 3;
    constant MI_RANDOM_ADDR_EN_BIT  : integer := 4;
    constant MI_ONE_SIMULT_READ_BIT : integer := 5;

    -- CTRL_OUT REG
    constant MI_TEST_DONE_BIT       : integer := 0;
    constant MI_TEST_SUCCESS_BIT    : integer := 1;
    constant MI_ECC_ERROR_BIT       : integer := 2;
    constant MI_CALIB_SUCCESS_BIT   : integer := 3;
    constant MI_CALIB_FAIL_BIT      : integer := 4;

    -- AMM_GEN
    -- in
    constant AMM_GEN_MEM_WR_BIT      : integer := 0;
    constant AMM_GEN_MEM_RD_BIT      : integer := 1;
    -- out
    constant AMM_GEN_BUFF_VLD_BIT    : integer := 2;
    constant AMM_GEN_AMM_READY_BIT   : integer := 3;

    -- AMM_PROBE
    -- in
    constant AMM_PROBE_RST_BIT      : integer := 0;
    constant AMM_PROBE_LATENCY_TO_FIRST_BIT : integer := 1;
    -- out
    -- TODO


    signal amm_clk                  : std_logic;
    signal mi_clk                   : std_logic;
    signal amm_rst                  : std_logic;
    signal mi_rst                   : std_logic;

    signal sim_done                 : std_logic := '0';

    -- Avalon interface for emif
    signal amm_ready                : std_logic                      := '0';
    signal amm_read                 : std_logic                      := '0';
    signal amm_write                : std_logic                      := '0';
    signal amm_address              : std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0)  := (others => '0');
    signal amm_read_data            : std_logic_vector(AMM_DATA_WIDTH - 1 downto 0) := (others => '0');
    signal amm_write_data           : std_logic_vector(AMM_DATA_WIDTH - 1 downto 0) := (others => '0');
    signal amm_burst_count          : std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0)   := (others => '0');
    signal amm_read_data_valid      : std_logic                      := '0';

    signal emif_rst_req             : std_logic;
    signal emif_rst_done            : std_logic;
    signal emif_ecc_isr             : std_logic;
    signal emif_cal_success         : std_logic;
    signal emif_cal_fail            : std_logic;

    -- MI32 interface
    signal mi32_dwr                 : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal mi32_addr                : std_logic_vector(MI_ADDR_WIDTH - 1 downto 0);
    signal mi32_be                  : std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0);
    signal mi32_rd                  : std_logic;
    signal mi32_wr                  : std_logic;
    signal mi32_ardy                : std_logic;
    signal mi32_drd                 : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal mi32_drdy                : std_logic;

    procedure toggleBit_p (addr_int : in integer; bit_pos : in integer; signal mi_status : inout TCommandStatus; constant mi_id : in integer)
    is
        variable addr : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
        variable data : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
        variable be   : std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0)    := (others => '1');

    begin
        addr := std_logic_vector(to_unsigned(addr_int, addr'length));

        -- Read previous state of the register, so other bits are not overwritten
        work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
        wait for 1 * MI_CLK_PERIOD;

        data(bit_pos) := '1';
        work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
        wait for 1 * MI_CLK_PERIOD;

        data(bit_pos) := '0';
        work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
        wait for 1 * MI_CLK_PERIOD;
    end procedure;

    procedure setBit_p (addr_int : in integer; bit_pos : in integer; val : in std_logic; signal mi_status : inout TCommandStatus; constant mi_id : in integer)
    is
        variable addr : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
        variable data : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
        variable be   : std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0)    := (others => '1');

    begin
        addr := std_logic_vector(to_unsigned(addr_int, addr'length));

        -- Read previous state of the register, so other bits are not overwritten
        work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
        wait for 1 * MI_CLK_PERIOD;

        data(bit_pos) := val;

        work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
        wait for 1 * MI_CLK_PERIOD;
    end procedure;

    procedure probe_res_p (signal mi_status : inout TCommandStatus; constant mi_id : in integer)
    is
        variable addr : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
        variable data : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
        variable be   : std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0)    := (others => '1');

    begin
        report "Probe results:";

        addr := std_logic_vector(to_unsigned(AMM_PROB_WR_TICKS_ADDR, addr'length));
        work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
        report "Write ticks: " & integer'image(to_integer(unsigned(data)));
        wait for 1 * MI_CLK_PERIOD;

        addr := std_logic_vector(to_unsigned(AMM_PROB_RD_TICKS_ADDR, addr'length));
        work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
        report "Read ticks: " & integer'image(to_integer(unsigned(data)));
        wait for 1 * MI_CLK_PERIOD;

        addr := std_logic_vector(to_unsigned(AMM_PROB_RW_TICKS_ADDR, addr'length));
        work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
        report "R/W ticks: " & integer'image(to_integer(unsigned(data)));
        wait for 1 * MI_CLK_PERIOD;

        addr := std_logic_vector(to_unsigned(AMM_PROB_WR_WORDS_ADDR, addr'length));
        work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
        report "Words written: " & integer'image(to_integer(unsigned(data)));
        wait for 1 * MI_CLK_PERIOD;

        addr := std_logic_vector(to_unsigned(AMM_PROB_RD_WORDS_ADDR, addr'length));
        work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
        report "Words read: " & integer'image(to_integer(unsigned(data)));
        wait for 1 * MI_CLK_PERIOD;

        addr := std_logic_vector(to_unsigned(AMM_PROB_REQ_WORDS_ADDR, addr'length));
        work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
        report "Words requested: " & integer'image(to_integer(unsigned(data)));
        wait for 1 * MI_CLK_PERIOD;

        addr := std_logic_vector(to_unsigned(AMM_PROB_LATENCY_SUM_1_ADDR, addr'length));
        work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
        report "Latency sum 1: " & integer'image(to_integer(unsigned(data)));
        wait for 1 * MI_CLK_PERIOD;

        addr := std_logic_vector(to_unsigned(AMM_PROB_LATENCY_SUM_2_ADDR, addr'length));
        work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
        report "Latency sum 2: " & integer'image(to_integer(unsigned(data)));
        wait for 1 * MI_CLK_PERIOD;

        addr := std_logic_vector(to_unsigned(AMM_PROB_LATENCY_MIN_ADDR, addr'length));
        work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
        report "Latency min: " & integer'image(to_integer(unsigned(data)));
        wait for 1 * MI_CLK_PERIOD;

        addr := std_logic_vector(to_unsigned(AMM_PROB_LATENCY_MAX_ADDR, addr'length));
        work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
        report "Latency max: " & integer'image(to_integer(unsigned(data)));
        wait for 1 * MI_CLK_PERIOD;

    end procedure;

    procedure amm_gen_test_p (start_addr : in integer; burst : in integer; test_fail : out std_logic; signal mi_status : inout TCommandStatus; constant mi_id : in integer)
    is
        variable addr : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
        variable data : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
        variable be   : std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0)    := (others => '1');

        variable test_fail_intern   : std_logic := '0';
        variable manual_wr_addr     : integer   := 0;
        variable manual_wr_data     : integer   := 0;

        -- TODO: use random data
        variable test_data_incr     : integer   := 42;
    begin
        -- Set burst
        addr := std_logic_vector(to_unsigned(AMM_GEN_BURST_ADDR, addr'length));
        data := std_logic_vector(to_unsigned(burst, data'length));
        work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);

        setBit_p(MI_CTRL_IN_ADDR, MI_MANUAL_EN_BIT, '1', mi_status, mi_id);

        manual_wr_data := 0;

        -- Fill buffer
        for b in 0 to burst - 1 loop
            for s in 0 to AMM_DATA_WIDTH / MI_DATA_WIDTH - 1 loop
                -- set address in mi2amm buffer
                addr := std_logic_vector(to_unsigned(AMM_GEN_ADDR_ADDR, addr'length));
                data := std_logic_vector(to_unsigned(b, data'length));
                work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
                wait for 1 * MI_CLK_PERIOD;

                addr := std_logic_vector(to_unsigned(AMM_GEN_SLICE_ADDR, addr'length));
                data := std_logic_vector(to_unsigned(s, data'length));
                work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
                wait for 1 * MI_CLK_PERIOD;

                -- set data
                addr := std_logic_vector(to_unsigned(AMM_GEN_DATA_ADDR, addr'length));
                data := std_logic_vector(to_unsigned(manual_wr_data, data'length));
                work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
                wait for 1 * MI_CLK_PERIOD;

                manual_wr_data := manual_wr_data + test_data_incr;
            end loop;
        end loop;

        -- set amm address for write
        addr := std_logic_vector(to_unsigned(AMM_GEN_ADDR_ADDR, addr'length));
        data := std_logic_vector(to_unsigned(start_addr, data'length));
        work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
        wait for 10 * MI_CLK_PERIOD;

        -- manually write to memory
        toggleBit_p(AMM_GEN_CTRL_ADDR, AMM_GEN_MEM_WR_BIT, mi_status, mi_id);

        manual_wr_addr := 0;
        manual_wr_data := 0;

        -- Clear buffer
        for b in 0 to burst - 1 loop
            for s in 0 to AMM_DATA_WIDTH / MI_DATA_WIDTH - 1 loop
                -- set address in mi2amm buffer
                addr := std_logic_vector(to_unsigned(AMM_GEN_ADDR_ADDR, addr'length));
                data := std_logic_vector(to_unsigned(b, data'length));
                work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
                wait for 1 * MI_CLK_PERIOD;

                addr := std_logic_vector(to_unsigned(AMM_GEN_SLICE_ADDR, addr'length));
                data := std_logic_vector(to_unsigned(s, data'length));
                work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
                wait for 1 * MI_CLK_PERIOD;

                -- set data
                addr := std_logic_vector(to_unsigned(AMM_GEN_DATA_ADDR, addr'length));
                data := std_logic_vector(to_unsigned(0, data'length));
                work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
                wait for 1 * MI_CLK_PERIOD;

                manual_wr_addr := manual_wr_addr + 1;
            end loop;
        end loop;

        manual_wr_addr := 0;
        manual_wr_data := 0;

        -- check that buffer is cleared
        for b in 0 to burst - 1 loop
            for s in 0 to AMM_DATA_WIDTH / MI_DATA_WIDTH - 1 loop
                -- set address in mi2amm buffer
                addr := std_logic_vector(to_unsigned(AMM_GEN_ADDR_ADDR, addr'length));
                data := std_logic_vector(to_unsigned(b, data'length));
                work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
                wait for 1 * MI_CLK_PERIOD;

                addr := std_logic_vector(to_unsigned(AMM_GEN_SLICE_ADDR, addr'length));
                data := std_logic_vector(to_unsigned(s, data'length));
                work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
                wait for 1 * MI_CLK_PERIOD;

                -- read data
                addr := std_logic_vector(to_unsigned(AMM_GEN_DATA_ADDR, addr'length));
                work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
                wait for 1 * MI_CLK_PERIOD;

                if (to_integer(unsigned(data)) /= 0) then
                    report "Data from manual r/w buffer was not cleared" severity ERROR;
                    test_fail_intern := '1';
                end if;

                manual_wr_addr := manual_wr_addr + 1;
            end loop;
        end loop;

        -- set amm address for read
        addr := std_logic_vector(to_unsigned(AMM_GEN_ADDR_ADDR, addr'length));
        data := std_logic_vector(to_unsigned(start_addr, data'length));
        work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
        wait for 1 * MI_CLK_PERIOD;

        toggleBit_p(AMM_GEN_CTRL_ADDR, AMM_GEN_MEM_RD_BIT, mi_status, mi_id);

        -- Wait for buffer data valid
        addr := std_logic_vector(to_unsigned(AMM_GEN_CTRL_ADDR, addr'length));
        work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
        while data(AMM_GEN_BUFF_VLD_BIT) /= '1' loop
            work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
            wait for 1 * MI_CLK_PERIOD;
        end loop;

        manual_wr_addr := 0;
        manual_wr_data := 0;

        -- read back all data
        for b in 0 to burst - 1 loop
            for s in 0 to AMM_DATA_WIDTH / MI_DATA_WIDTH - 1 loop
                -- set address in mi2amm buffer
                addr := std_logic_vector(to_unsigned(AMM_GEN_ADDR_ADDR, addr'length));
                data := std_logic_vector(to_unsigned(b, data'length));
                work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
                wait for 1 * MI_CLK_PERIOD;

                addr := std_logic_vector(to_unsigned(AMM_GEN_SLICE_ADDR, addr'length));
                data := std_logic_vector(to_unsigned(s, data'length));
                work.mi_sim_pkg.WriteData(addr, data, be, mi_status, mi_id);
                wait for 1 * MI_CLK_PERIOD;

                -- read data
                addr := std_logic_vector(to_unsigned(AMM_GEN_DATA_ADDR, addr'length));
                work.mi_sim_pkg.ReadData(addr, data, be, mi_status, mi_id);
                wait for 1 * MI_CLK_PERIOD;

                if (to_integer(unsigned(data)) /= manual_wr_data) then
                    report "Data from manual r/w test do not match " &
                            "(data: " & integer'image(to_integer(unsigned(data))) & ")" &
                            "(requested: " & integer'image(manual_wr_data) & ")"
                            severity ERROR;
                    test_fail_intern := '1';
                end if;

                manual_wr_addr := manual_wr_addr + 1;
                manual_wr_data := manual_wr_data + test_data_incr;
            end loop;
        end loop;

        if (test_fail_intern = '0') then
            report "Manual r/w succesfull";
        end if;

        test_fail := test_fail_intern;
    end procedure;


begin

    ---------
    -- UUT --
    ---------

    uut : entity work.MEM_TESTER
    generic map(
        -- Avalon bus
        AMM_DATA_WIDTH          => AMM_DATA_WIDTH,
        AMM_ADDR_WIDTH          => AMM_ADDR_WIDTH,
        AMM_BURST_COUNT_WIDTH   => AMM_BURST_COUNT_WIDTH,

        -- MI bus
        MI_DATA_WIDTH           => MI_DATA_WIDTH,
        MI_ADDR_WIDTH           => MI_ADDR_WIDTH,

        RAND_GEN_DATA_WIDTH         => 64,
        RAND_GEN_ADDR_WIDTH         => 26,
        RANDOM_DATA_SEED            =>
            (
                X"04a90474c868e517",
                X"8b9d55e316e57bfc",
                X"0554f750a3702377",
                X"abcd76981c982117",
                X"fc21f22c3ad6d735",
                X"5d06b6ae01cf86f8",
                X"38fc9671a56bb8e8",
                X"38fc9671a56bb8e8",
                X"457a2fb6bd25f1fa"
            ),
        RANDOM_ADDR_SEED            => X"FEFE01" & "01",

        DEFAULT_ADDR_LIMIT      => ADDR_LIMIT,
        DEFAULT_BURST_CNT       => DEFAULT_BURST_CNT,
        DEBUG_RAND_ADDR         => True,

        DEVICE                  => DEVICE
    )
    port map(
        -- Avalon interface from EMIF IP
        AMM_CLK                 => amm_clk,
        AMM_RST                 => amm_rst,
        AMM_READY               => amm_ready,
        AMM_READ                => amm_read,
        AMM_WRITE               => amm_write,
        AMM_ADDRESS             => amm_address,
        AMM_READ_DATA           => amm_read_data,
        AMM_WRITE_DATA          => amm_write_data,
        AMM_BURST_COUNT         => amm_burst_count,
        AMM_READ_DATA_VALID     => amm_read_data_valid,

        EMIF_RST_REQ            => emif_rst_req,
        EMIF_RST_DONE           => emif_rst_done,
        EMIF_ECC_ISR            => emif_ecc_isr,
        EMIF_CAL_SUCCESS        => emif_cal_success,
        EMIF_CAL_FAIL           => emif_cal_fail,

        -- MI bus signals
        MI_CLK                  => mi_clk,
        MI_RST                  => mi_rst,
        MI_DWR                  => mi32_dwr,
        MI_ADDR                 => mi32_addr,
        MI_BE                   => mi32_be,
        MI_RD                   => mi32_rd,
        MI_WR                   => mi32_wr,
        MI_ARDY                 => mi32_ardy,
        MI_DRD                  => mi32_drd,
        MI_DRDY                 => mi32_drdy
    );

    --------------
    -- EMIF SIM --
    --------------

    emif_sim_i : entity work.EMIF_SIM
    generic map(
        AMM_DATA_WIDTH          => AMM_DATA_WIDTH,
        AMM_ADDR_WIDTH          => AMM_ADDR_WIDTH,
        AMM_BURST_COUNT_WIDTH   => AMM_BURST_COUNT_WIDTH,

        CLK_PERIOD              => AMM_CLK_PERIOD,
        MEM_SIZE                => MEM_SIZE
    )
    port map(
        CLK                     => amm_clk,
        RST                     => amm_rst,

        AMM_READY               => amm_ready,
        AMM_READ                => amm_read,
        AMM_WRITE               => amm_write,
        AMM_ADDRESS             => amm_address,
        AMM_READ_DATA           => amm_read_data,
        AMM_WRITE_DATA          => amm_write_data,
        AMM_BURST_COUNT         => amm_burst_count,
        AMM_READ_DATA_VALID     => amm_read_data_valid,

        EMIF_RST_REQ            => emif_rst_req,
        EMIF_RST_DONE           => emif_rst_done,
        EMIF_ECC_ISR            => emif_ecc_isr,
        EMIF_CAL_SUCCESS        => emif_cal_success,
        EMIF_CAL_FAIL           => emif_cal_fail,

        RANDOM_AMM_READY        => '1'
    );

    -------------------------------
    -- MI32 simulation component --
    -------------------------------

   mi_sim_i : entity work.MI_SIM
   generic map (
      MI_SIM_ID                 => 0
   )
   port map (
      CLK                       => mi_clk,
      RESET                     => mi_rst,

      MI32_DWR                  => mi32_dwr,
      MI32_ADDR                 => mi32_addr,
      MI32_BE                   => mi32_be,
      MI32_RD                   => mi32_rd,
      MI32_WR                   => mi32_wr,
      MI32_ARDY                 => mi32_ardy,
      MI32_DRD                  => mi32_drd,
      MI32_DRDY                 => mi32_drdy
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

    mi_clk_gen_p : process
    begin
        if (sim_done = '1') then
            wait;
        end if;

        mi_clk <= '1';
        wait for MI_CLK_PERIOD / 2;
        mi_clk <= '0';
        wait for MI_CLK_PERIOD / 2;
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

    mi_reset_gen_p : process
    begin
        if (sim_done = '1') then
            wait;
        end if;

        mi_rst <= '1';
        wait for MI_RST_INIT_TIME;
        mi_rst <= '0';
        wait;
    end process;

    mi_test_p : process
        variable addr               : std_logic_vector(MI_DATA_WIDTH - 1 downto 0)        := (others => '0');
        variable data               : std_logic_vector(MI_DATA_WIDTH - 1 downto 0)        := (others => '0');
        variable be                 : std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0)    := (others => '1');
        variable test_done          : std_logic := '0';
        variable seq_test_fail      : std_logic := '0';
        variable rand_test_fail     : std_logic := '0';
        variable manual_test_fail   : std_logic := '0';
    begin
        sim_done            <= '0';

        wait until mi_rst = '0' and amm_rst = '0';
        wait for 10 * MI_CLK_PERIOD;

        ----------------------------------
        -- Run memory test (sequential) --
        ----------------------------------
        test_done := '0';
        -- force reset via MI bus
        toggleBit_p(MI_CTRL_IN_ADDR, MI_RST_BIT, status(0), 0);
        wait for 5 * MI_CLK_PERIOD;


        addr := std_logic_vector(to_unsigned(MI_REFRESH_PERIOD_ADDR, addr'length));
        data := std_logic_vector(to_unsigned(20, data'length));
        work.mi_sim_pkg.WriteData(addr, data, be, status(0),0);
        wait for 1 * MI_CLK_PERIOD;

        -- To measure to first response data (default to last response data)
        --setBit_p(AMM_PROB_CTRL_ADDR, AMM_PROBE_LATENCY_TO_FIRST_BIT, '1', status(0), 0);

        -- run test
        toggleBit_p(MI_CTRL_IN_ADDR, MI_RUN_TEST_BIT, status(0), 0);

        --for tries in 1 to 10 loop
        while test_done = '0' loop
            addr := std_logic_vector(to_unsigned(MI_CTRL_OUT_ADDR, addr'length));
            ReadData(addr, data, be, status(0), 0);

            --report "Received data: " & to_string(data(7 downto 0));

            if (data(MI_TEST_DONE_BIT) = '1') then
                if data(MI_TEST_SUCCESS_BIT) = '1' then
                    report "Memory sequential test successful";
                else
                    report "Memory test failed" severity ERROR;
                    seq_test_fail   := '1';
                end if;

                test_done := '1';
            end if;
            wait for 10 * MI_CLK_PERIOD;
        end loop;

        -----------------------
        -- AMM probe results --
        -----------------------
        --probe_res_p(status(0), 0);

        -- Test histogrammer
        -- for i in 0 to 512 - 1 loop
        --     addr := std_logic_vector(to_unsigned(AMM_PROB_HIST_SEL, addr'length));
        --     data := std_logic_vector(to_unsigned(i, data'length));
        --     work.mi_sim_pkg.WriteData(addr, data, be, status(0),0);
        --     wait for 1 * MI_CLK_PERIOD;
        -- end loop;

        -----------------------------------
        -- Run memory test (random addr) --
        -----------------------------------
        test_done := '0';
        -- force reset via MI bus
        toggleBit_p(MI_CTRL_IN_ADDR, MI_RST_BIT, status(0), 0);
        wait for 5 * MI_CLK_PERIOD;

        -- Set random indexing
        setBit_p(MI_CTRL_IN_ADDR, MI_RANDOM_ADDR_EN_BIT, '1', status(0), 0);

        -- run test
        toggleBit_p(MI_CTRL_IN_ADDR, MI_RUN_TEST_BIT, status(0), 0);

        --for tries in 1 to 10 loop
        while test_done = '0' loop
            addr := std_logic_vector(to_unsigned(MI_CTRL_OUT_ADDR, addr'length));
            ReadData(addr, data, be, status(0), 0);

            --report "Received data: " & to_string(data(7 downto 0));

            if (data(MI_TEST_DONE_BIT) = '1') then
                if data(MI_TEST_SUCCESS_BIT) = '1' then
                    report "Memory random indexing test successful";
                else
                    report "Memory test failed - corrent during random indexing";
                    rand_test_fail  := '0';
                end if;

                test_done := '1';
            end if;
            wait for 10 * MI_CLK_PERIOD;
        end loop;

        -----------------------
        -- AMM probe results --
        -----------------------
        ---probe_res_p(status(0), 0);

        -- force reset via MI bus
        toggleBit_p(MI_CTRL_IN_ADDR, MI_RST_BIT, status(0), 0);
        wait for 5 * MI_CLK_PERIOD;

        ------------------------------------------------
        -- Run memory test (only 1 simultaneous read) --
        ------------------------------------------------
        report "Running one sumult read test";

        test_done := '0';
        -- force reset via MI bus
        toggleBit_p(MI_CTRL_IN_ADDR, MI_RST_BIT, status(0), 0);
        wait for 5 * MI_CLK_PERIOD;

        setBit_p(MI_CTRL_IN_ADDR, MI_ONE_SIMULT_READ_BIT, '1', status(0), 0);

        -- run test
        toggleBit_p(MI_CTRL_IN_ADDR, MI_RUN_TEST_BIT, status(0), 0);

        --for tries in 1 to 10 loop
        while test_done = '0' loop
            addr := std_logic_vector(to_unsigned(MI_CTRL_OUT_ADDR, addr'length));
            ReadData(addr, data, be, status(0), 0);

            if (data(MI_TEST_DONE_BIT) = '1') then
                if data(MI_TEST_SUCCESS_BIT) = '1' then
                    report "Memory 1 simult read test successful";
                else
                    report "Memory test failed" severity ERROR;
                    rand_test_fail  := '0';
                end if;

                test_done := '1';
            end if;
            wait for 10 * MI_CLK_PERIOD;
        end loop;

        -----------------------
        -- AMM probe results --
        -----------------------
        -- probe_res_p(status(0), 0);

        -- force reset via MI bus
        toggleBit_p(MI_CTRL_IN_ADDR, MI_RST_BIT, status(0), 0);
        wait for 50 * MI_CLK_PERIOD;

        --------------------------------
        -- Manual avalon control test --
        --------------------------------

        report "Running manual control test";

        amm_gen_test_p(0, 50, manual_test_fail, status(0), 0);
        amm_gen_test_p(7, 7,  manual_test_fail, status(0), 0);
        amm_gen_test_p(2, 16,  manual_test_fail, status(0), 0);
        amm_gen_test_p(3, 1,  manual_test_fail, status(0), 0);
        amm_gen_test_p(1, 50,  manual_test_fail, status(0), 0);

        -------------------------------
        -- Wrong address access test --
        -------------------------------

        addr := std_logic_vector(to_unsigned(AMM_GEN_BURST_ADDR + 4, addr'length));
        ReadData(addr, data, be, status(0), 0);

        if (data /= X"DEADBEEF") then
            report "No DEADBEEF when accessing wrong address";
        end if;

        if (seq_test_fail = '1' or rand_test_fail = '1' or manual_test_fail = '1') then
            report "|| Simulation FAILED ||";
        else
            report "|| Simulation SUCCESFULL ||";
        end if;
        sim_done    <= '1';
        wait;

    end process;
end architecture;




