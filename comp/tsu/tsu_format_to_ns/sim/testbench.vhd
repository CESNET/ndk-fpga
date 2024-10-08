-- testbench.vhd.
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use std.env.all;
use STD.textio.all;

library work;
use work.type_pack.all;
use work.math_pack.all;
use work.basics_test_pkg.all;
use std.env.stop;
use STD.textio.all;

-- ============================================================================
--                        Entity declaration
-- ============================================================================
entity TESTBENCH is
end entity TESTBENCH;
-- ============================================================================
--                      Architecture declaration
-- ============================================================================
architecture BEHAVIORAL of TESTBENCH is

    -- DUT Register bitmap
    constant REG_BITMAP       : std_logic_vector(2 downto 0) := "101";
    -- DUT latency
    constant CLOCK_CYCLES     : natural := count_ones(REG_BITMAP);
    -- set to true for more detailed reports in the Transcript window
    -- Options: 0 (no report), 1 (only when error occurs), 2 (for each transaction)
    constant VERBOSE          : natural := 1;
    -- writes a report about the number of correct results to the Transcript window every Nth iteration
    constant REPORT_EVERY_NTH : natural := 10;
    -- number of clock cycles the simulation should run for
    constant LENGHT_OF_SIM    : natural := 1000;
    constant CLK_PERIOD       : time    := 10 ns;

    -- setting signals
    signal clk                     : std_logic;
    signal rst                     : std_logic;
    signal tsu_ts                  : slv_array_t     (CLOCK_CYCLES downto 0)(64-1 downto 0) := (others => (others => '0'));
    signal dut_ns                  : std_logic_vector                       (64-1 downto 0);
    signal model_ns                : unsigned                               (64-1 downto 0) := (others => '0');

    -- signals for verification of a successful run
    signal stop_at_the_end         : std_logic := '0'; -- is '1' at the end of the simulation, allows for the verdict of the simulation run to be written out
    signal clk_cycle_count         : natural := 0; -- +1 each rising edge, counts up until the LENGHT_OF_SIM is reached
    signal correct_results         : natural := 0; -- counts the number of iterations when results from the testbench and from the DUT were equal
    signal incorrect_results       : natural := 0; -- counts the number of iterations when results from the testbench and from the DUT were not equal

    shared variable l : line;

begin

    uut : entity work.TSU_FORMAT_TO_NS
    generic map (
        REG_BITMAP => REG_BITMAP
    )
    port map (
        CLK    => clk      ,
        RESET  => rst      ,
        TS_TSU => tsu_ts(0),
        TS_NS  => dut_ns
    );

    --  ========================================================================
    --  Setting control signals
    --  ========================================================================

    -- generating clock signal
    clock_p : process
    begin
        if (clk_cycle_count-5 < LENGHT_OF_SIM) then
            clk <= '1';
            wait for CLK_PERIOD/2;
            clk <= '0';
            wait for CLK_PERIOD/2;
        else
            wait;
        end if;
    end process;

    -- counting the number of clock cycles
    clk_cycle_count_p : process
    begin
        wait until rising_edge(clk);
        if (rst = '0') then
            if (clk_cycle_count+1 < LENGHT_OF_SIM) then
                clk_cycle_count <= clk_cycle_count + 1;
            else
                stop_at_the_end <= '1';
                wait;
            end if;
        else
            wait until (rst = '0');
        end if;
    end process;

    -- randomly asserting rst
    rst_p : process
        -- variable s0 : integer := 7;
        -- variable s1 : integer := 4;
        -- variable X  : integer := 2;
    begin
        rst <= '1';
        wait for 3*CLK_PERIOD;
        wait for 0.13*CLK_PERIOD;
        rst <= '0';
        -- rst_rand_gen_l : for i in 0 to LENGHT_OF_SIM loop
        --     if (stop_at_the_end = '0') then
        --         -- generate random times to assert rst
        --         randint(s0, s1, 5, 15, X);
        --         wait for (i+1)*CLK_PERIOD*X*X;
        --         rst <= '1';
        --         wait for 3*CLK_PERIOD;
        --         rst <= '0';
        --     else
        --         wait;
        --     end if;
        -- end loop;
        wait;
    end process;

    --  ========================================================================
    --  Generating random input
    --  ========================================================================

    gen_seconds_p : process
        variable seed1 : positive := 2;
        variable seed2 : positive := 3;
        variable seed  : positive;
        variable s     : std_logic_vector(64-1 downto 0);
    begin
        wait until rising_edge(clk);
        if (rst = '0') then
            if (stop_at_the_end = '0') then
                    randint(seed1,seed2,2,20,seed);
                    tsu_ts(0) <= (random_vector(64, seed));
                    -- write(l, "Generated number of seconds (tsu_ts(0)): " & integer'image(to_integer(unsigned(tsu_ts(0))))); writeline(output, l);
                for c in 0 to CLOCK_CYCLES-1 loop
                    tsu_ts(c+1) <= tsu_ts(c);
                end loop;
            else
                wait;
            end if;
        else
            wait until (rst = '0');
        end if;
    end process;

    --  ========================================================================
    --  Evaluation
    --  ========================================================================

    evaluation_p : process
        variable tsu_ns_conv : unsigned(64-1 downto 0);
        variable tsu_ns      : unsigned(64-1 downto 0);
    begin
        wait until rising_edge(clk);
        if (rst = '0') then
            -- conversion to [ns]
            tsu_ns_conv := resize(unsigned(tsu_ts(CLOCK_CYCLES-1)(63 downto 32)) * to_unsigned(10**9, log2(10**9)),64);
            tsu_ns      := resize(unsigned(tsu_ts(CLOCK_CYCLES-1)(31 downto  0)),64);
            model_ns <= tsu_ns_conv + tsu_ns;
            if (stop_at_the_end = '0') then
                if (VERBOSE=2) then
                    write(l, "Input [seconds]: "   & to_string(tsu_ts(CLOCK_CYCLES-1)(63 downto 32)) & " ");
                    write(l, "Input [ns]     : "   & to_string(tsu_ts(CLOCK_CYCLES-1)(31 downto  0)) & LF );
                    write(l, "Model output [ns]: " & to_string(model_ns)                             & LF );
                    write(l, "DUT   output [ns]: " & to_string(dut_ns)                                    );
                    writeline(output, l);
                end if;
                if (model_ns /= unsigned(dut_ns)) then
                    if (VERBOSE=1) then
                        write(l, "Error! " & LF);
                        write(l, to_string(tsu_ts(CLOCK_CYCLES-1)(63 downto 32)) & " seconds and " & LF);
                        write(l, to_string(tsu_ts(CLOCK_CYCLES-1)(31 downto  0)) & " nanoseconds " & LF);
                        write(l, "should equal to " & to_string(model_ns)                          & LF);
                        write(l, "and NOT to      " & to_string(dut_ns));
                        writeline(output, l);
                    end if;
                    incorrect_results <= incorrect_results + 1;
                else
                    correct_results <= correct_results + 1;
                end if;
            else
                wait;
            end if;
        else
            wait until (rst = '0');
        end if;
    end process;

    sim_verdict_p : process
    begin
        wait until stop_at_the_end = '1';
        if (incorrect_results = 0) then
            write(l, "VERIFICATION SUCCESS" & LF);
        else
            write(l, "There were " & integer'image(incorrect_results) & " incorrect results!" & LF);
        end if;
        write(l, "Compared transactions: " & integer'image(correct_results+incorrect_results));
        writeline(output, l);
        finish;
    end process;

end architecture;
