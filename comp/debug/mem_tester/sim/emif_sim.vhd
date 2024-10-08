-- emif_sim.vhd: Component for simulation of EMIF IP
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use ieee.math_real.all;
use work.math_pack.all;
use work.type_pack.all;


entity EMIF_SIM is
generic (
    AMM_DATA_WIDTH          : integer := 512;
    AMM_ADDR_WIDTH          : integer := 26;
    AMM_BURST_COUNT_WIDTH   : integer := 7;

    CLK_PERIOD              : time;
    -- to reduce simulation memory usage
    MEM_SIZE                : integer
);
port(
    CLK                     : in    std_logic;
    RST                     : in    std_logic;

    AMM_READY               : out   std_logic;
    AMM_READ                : in    std_logic;
    AMM_WRITE               : in    std_logic;
    AMM_ADDRESS             : in    std_logic_vector(AMM_ADDR_WIDTH - 1           downto 0);
    AMM_READ_DATA           : out   std_logic_vector(AMM_DATA_WIDTH - 1           downto 0);
    AMM_WRITE_DATA          : in    std_logic_vector(AMM_DATA_WIDTH - 1           downto 0);
    AMM_BURST_COUNT         : in    std_logic_vector(AMM_BURST_COUNT_WIDTH - 1    downto 0);
    AMM_READ_DATA_VALID     : out   std_logic;

    -- =====================
    -- Other EMIF IP signals
    --
    -- TODO: simulate there signals
    -- =====================

    EMIF_RST_REQ            : in    std_logic;
    EMIF_RST_DONE           : out   std_logic;
    EMIF_ECC_ISR            : out   std_logic;
    EMIF_CAL_SUCCESS        : out   std_logic;
    EMIF_CAL_FAIL           : out   std_logic;

    -- =============
    -- Debug signals
    -- =============

    -- On off random AMM_READY generation
    RANDOM_AMM_READY        : in   std_logic    := '1'
);
end entity;

architecture FULL of EMIF_SIM is
    constant MEM_INIT_TIME                  : time := CLK_PERIOD * 4;
    -- Max random CLK cycles cnt of AMM READY being at 0
    constant NOT_READY_MAX_DELAY            : integer := 20;
    -- Max random period of asserting AMM READY to 0 for random time
    constant NOT_READY_MAX_PERIOD           : integer := 20;

    constant NOT_VALID_MAX_DELAY            : integer := 100;
    constant NOT_VALID_MAX_DELAY_CHANCE     : real := 0.1;

    constant MEM_READ_TIME                  : time := CLK_PERIOD * 4;

    type States is (
        INIT,
        DATA_WRITE,
        DATA_READ,
        WAITING_READ,
        WAITING_WRITE,
        WAITING
    );

    -- state machine
    signal curr_state           : States;
    signal next_state           : States;

    -- each index has own data word
    signal mem                  : slv_array_t(0 to MEM_SIZE - 1)(AMM_DATA_WIDTH - 1 downto 0);
    signal mem_init             : std_logic := '1';
    signal emif_random_wait     : std_logic;

    signal ready                : std_logic;

    -- r/w control
    signal mem_read             : std_logic := '0';

    -- other
    signal error_occured        : std_logic := '0';

begin
    ----------------
    -- Wire logic --
    ----------------

    ready <= '1' when (mem_init = '0' and error_occured = '0' and emif_random_wait = '0')
             else '0';

    AMM_READY <= ready;
    EMIF_ECC_ISR <= '0';

    error_occured <= '1' when (AMM_READ = '1' and AMM_WRITE = '1')
                    else '0';

    -------------------
    -- R / W control --
    -------------------
    random_wait_p : process
        variable seed_1, seed_2     : positive;
        variable r                  : real;
        variable wait_clk_cycles    : integer;
    begin
        if (RANDOM_AMM_READY = '1') then
            emif_random_wait <= '1';
            uniform(seed_1, seed_2, r);
            wait_clk_cycles := integer(round(r * real(NOT_READY_MAX_DELAY + 1) - 0.5));
            wait for time'val(wait_clk_cycles * time'pos(CLK_PERIOD));
            emif_random_wait <= '0';

            uniform(seed_1, seed_2, r);
            wait_clk_cycles := integer(round(r * real(NOT_READY_MAX_PERIOD + 1) - 0.5));
            wait for time'val(wait_clk_cycles * time'pos(CLK_PERIOD));
        else
            emif_random_wait <= '0';
        end if;

        -- To stop simulation when clk stops
        wait until rising_edge(CLK);
    end process;


    write_ctrl_p : process
        variable write_start_addr   : integer;
        variable write_addr         : integer;

    begin
        wait until (ready = '1' and AMM_WRITE = '1' and rising_edge(CLK));
        for b in 0 to (to_integer(unsigned(AMM_BURST_COUNT)) - 1) loop
            if (b = 0) then
                write_start_addr    := to_integer(unsigned(AMM_ADDRESS));
            else
                wait until (ready = '1' and AMM_WRITE = '1' and rising_edge(CLK));
            end if;

            write_addr              := write_start_addr + b;
            mem(write_addr)         <= AMM_WRITE_DATA;
        end loop;
    end process;

    mem_read <= '1' when (ready = '1' and AMM_READ = '1') else '0';

    ----------------------------------
    -- Simulation of reset and init --
    ----------------------------------

    init_p : process
    begin
        --wait until (falling_edge(RST));
        wait until (falling_edge(RST)           and EMIF_RST_REQ = '0') or
                   (falling_edge(EMIF_RST_REQ)  and RST = '0')          or
                   (falling_edge(EMIF_RST_REQ)  and falling_edge(RST));

        EMIF_RST_DONE <= '0';
        mem_init <= '1';
        wait for MEM_INIT_TIME;

        EMIF_RST_DONE <= '1',
                         '0' after CLK_PERIOD * 1.5;
        mem_init <= '0';
    end process;

    -- Check that user reset request has at least 2 CLK cycles
    user_rst_p : process
    begin
        -- User forcing EMIF to reset
        wait until (RST = '0' and EMIF_RST_REQ = '1' and rising_edge(CLK));

        wait until rising_edge(CLK);
        wait until rising_edge(CLK);

        assert EMIF_RST_REQ = '1'
            report "EMIF user reset request has to be at least 2 CLK cycles at '1'!"
            severity error;

        wait until EMIF_RST_REQ = '0' and rising_edge(CLK);
    end process;

    calib_result_p : process
    begin
        EMIF_CAL_SUCCESS    <= '0';
        EMIF_CAL_FAIL       <= '0';

        wait until falling_edge(mem_init);

        EMIF_CAL_SUCCESS    <= '1';
        EMIF_CAL_FAIL       <= '0';
    end process;

    ------------------------------
    -- Memory access simulation --
    ------------------------------

    read_p : process
        variable last_readed_data_time : time := 0 ns;

        variable seed_1, seed_2     : positive;
        variable r                  : real;
        variable wait_clk_cycles    : integer;
    begin
        wait until rising_edge(CLK);

        if (RST = '1') then
            AMM_READ_DATA_VALID <= '0';
        elsif (mem_read = '1') then
            for burst in 0 to (to_integer(unsigned(AMM_BURST_COUNT)) - 1) loop

                if (last_readed_data_time < now) then
                    last_readed_data_time := now + MEM_READ_TIME + burst * CLK_PERIOD + CLK_PERIOD / 4;
                    -- CLK_PERIOD / 4 <- to avoid bad timing
                end if;

                uniform(seed_1, seed_2, r);
                if (r < NOT_VALID_MAX_DELAY_CHANCE) then
                    uniform(seed_1, seed_2, r);
                    wait_clk_cycles := integer(round(r * real(NOT_VALID_MAX_DELAY + 1) - 0.5));
                    last_readed_data_time := last_readed_data_time + CLK_PERIOD * wait_clk_cycles;
                end if;

                AMM_READ_DATA <= transport mem(to_integer(unsigned(AMM_ADDRESS)) + burst) after last_readed_data_time - now;

                AMM_READ_DATA_VALID <= transport '1' after (last_readed_data_time              - now);
                AMM_READ_DATA_VALID <= transport '0' after (last_readed_data_time + CLK_PERIOD - now);

                last_readed_data_time := last_readed_data_time + CLK_PERIOD;
            end loop;
        end if;
    end process;

end architecture;
