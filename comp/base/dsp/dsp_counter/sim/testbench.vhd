-- testbench.vhd.
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use std.env.all;
use STD.textio.all;

library work;
use work.basics_test_pkg.all;


-- NOTE: When the rst signal deasserts at the exact time as clk asserts (happens very rarely) and when DSPs are enabled, the simulation ends with an error,
--       it seems like it is because the DSP does not react in time and starts counting one cycle later that it should - identified on Stratix 10 only (probably Agilex too).

-- Another NOTE: Please beware that the counter on Xilix with DSPs enabled has different latency for each extra chained DSP block and reacts later on CE and reset signals
--               1 DSP has max OUTPUT_WIDTH=48, chaining each other DSP results in latency+1,
--               this simulation does not give correct results with more than 2 chained DSPs
--               rather than reading comments I recommend running the simulation and studying the wave diagram

-- ============================================================================
--                        Entity declaration
-- ============================================================================
entity TESTBENCH is
end entity TESTBENCH;
-- ============================================================================
--                      Architecture declaration
-- ============================================================================
architecture BEHAVIORAL of TESTBENCH is

    -- target device: STRATIX10 (Intel), AGILEX (Intel), 7SERIES (Xilinx), ULTRASCALE (Xilinx)
    constant DEVICE        : string  := "AGILEX";
    constant INPUT_REGS    : boolean := true;
    constant INPUT_WIDTH   : natural := 27;
    constant OUTPUT_WIDTH  : natural := 64;
    constant DSP_ENABLE    : boolean := true;
    -- number of clock cycles the simulation should run for - this must concur with the length of sumulation defined in sim_sig.fdo ("run ... us")
    constant LENGHT_OF_SIM : natural := 100000;
    constant CLK_PERIOD : time := 10 ns;

    -- setting signals
    signal clk     : std_logic;
    signal clk_ena : std_logic;
    signal rst     : std_logic;
    signal cnt_by  : std_logic_vector(INPUT_WIDTH-1 downto 0);
    signal max     : std_logic_vector(OUTPUT_WIDTH-1 downto 0) := (others => '1'); -- (others => '1'), no other values are supported

    signal cnt_result : std_logic_vector(OUTPUT_WIDTH-1 downto 0); -- output of the tested counter

    -- other signals
    signal clk_cycle_count   : natural := 0;
    signal stop_at_the_end   : std_logic := '0'; -- stops the simulation when LENGHT_OF_SIM is reached

    -- signals to simulate the counter
    signal cnt_by_behind_regs      : std_logic_vector(INPUT_WIDTH-1 downto 0); -- this signal helps to adjust to the wierd latency of Xilinx DSP counter
    signal cnt_by_behind_all_regs  : std_logic_vector(INPUT_WIDTH-1 downto 0); -- if input register is enabled, cnt_by signal must be delayed
    signal clk_ena_behind_regs     : std_logic; -- this signal helps to adjust to the wierd latency of Xilinx DSP counter
    signal clk_ena_behind_all_regs : std_logic; -- if input register is enabled, clk_ena signal must be delayed as well
    signal rst_behind_regs         : std_logic; -- this signal helps to adjust to the wierd latency of Xilinx DSP counter
    signal sim_result              : std_logic_vector(OUTPUT_WIDTH-1 downto 0) := (others => '0'); -- result of the simulated counter

    -- signals to evaluate correct functioning of the counter
    signal correct_results   : integer := 1; -- counts successful iterations
    signal incorrect_results : integer := 1; -- counts incorrect results
    signal result_ok         : std_logic; -- the result from comparing the simulation result with the counter result

    shared variable l : line;

begin

    uut : entity work.DSP_COUNTER
    generic map (
        DEVICE       => DEVICE      ,
        INPUT_REGS   => INPUT_REGS  ,
        INPUT_WIDTH  => INPUT_WIDTH ,
        OUTPUT_WIDTH => OUTPUT_WIDTH,
        DSP_ENABLE   => DSP_ENABLE
    )
    port map(
        CLK        => clk    ,
        CLK_EN     => clk_ena,
        RESET      => rst    ,
        INCREMENT  => cnt_by ,
        MAX_VAL    => max    ,
        RESULT     => cnt_result
    );

    -- ========================================================================
    -- Setting simulation signals
    -- ========================================================================
    -- generating clk0
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
        if (clk_cycle_count+1 < LENGHT_OF_SIM) then
            clk_cycle_count <= clk_cycle_count + 1;
        else
            stop_at_the_end <= '1';
            wait;
        end if;
    end process;

    -- randomly asserting clk_ena
    clk_ena_p : process
        variable s0 : integer := 3;
        variable s1 : integer := 2;
        variable X  : integer := 6;
    begin
        clk_ena <= '0';
        wait until rst = '0';
        wait for 0.5*CLK_PERIOD;
        clk_ena <= '1';
        clk_ena_rand_gen_l : for i in 0 to 1000 loop
            if (stop_at_the_end = '0') then
                -- generate random times to assert and deassert clk_ena
                randint(s0, s1, 2, 10, X);
                wait for (i+1)*CLK_PERIOD*X;
                clk_ena <= '0';
                wait for 2*CLK_PERIOD;
                clk_ena <= '1';
            else
                wait;
            end if;
        end loop;
        wait;
    end process;

    -- randomly asserting rst
    rst_p : process
        variable s0 : integer := 7;
        variable s1 : integer := 3;
        variable X  : integer := 2;
    begin
        rst <= '1';
        wait for 3*CLK_PERIOD;
        wait for 0.13*CLK_PERIOD;
        rst <= '0';
        rst_rand_gen_l : for i in 0 to 100 loop
            if (stop_at_the_end = '0') then
                -- generate random times to assert rst
                randint(s0, s1, 5, 15, X);
                wait for (i+1)*CLK_PERIOD*X*X;
                rst <= '1';
                wait for 3*CLK_PERIOD;
                rst <= '0';
            else
                wait;
            end if;
        end loop;
        wait;
    end process;

    -- generating random input for the counter
    rand_cnt_by_p : process
        variable s0 : integer := 8;
        variable s1 : integer := 9;
        variable X  : integer := 4;
    begin
        if (stop_at_the_end = '0') then
            wait until rising_edge(clk);
            -- generating random integer
            randint(s0, s1, 1, integer'high, X);
            wait for 0.1*CLK_PERIOD;
            -- using the randomly generated integer (X) to generate a random std_logic_vector
            cnt_by <= random_vector(INPUT_WIDTH, X);
        else
            wait;
        end if;
    end process;

    -- ========================================================================
    -- Simulated counter
    -- ========================================================================
    -- in case of counter on Xilinx device using DSPs, the latency is + 1 (=> 2 or 3)
    counter_latency_variation_g : if (((DEVICE /= "STRATIX10") and (DEVICE /= "AGILEX")) and (DSP_ENABLE = true) and (OUTPUT_WIDTH > 48)) generate

        -- the CE is delayed when going through the DSP, it is also reset
        clk_ena_dly_p : process (clk)
        begin
            if (rising_edge(clk)) then
                if (rst = '1') then
                    clk_ena_behind_regs <= '0';
                    clk_ena_behind_all_regs <= '0';
                else
                    clk_ena_behind_regs <= clk_ena;
                    clk_ena_behind_all_regs <= clk_ena_behind_regs;
                end if;
            end if;
        end process;

        -- rst is also delayed going through the counter
        rst_dly_p : process (clk)
        begin
            if (rising_edge(clk)) then
                rst_behind_regs <= rst;
            end if;
        end process;

        input_regs_g : if (INPUT_REGS = false) generate

            -- this is the input register, enabled by the undelayed CE
            cnt_by_dly1_p : process (clk)
            begin
                if (rising_edge(clk)) then
                    if (rst = '1') then
                        cnt_by_behind_all_regs <= (others => '0');
                    elsif (clk_ena_behind_regs = '1') then
                        cnt_by_behind_all_regs <= cnt_by;
                    end if;
                end if;
            end process;

        else generate

            -- this is the 1st register - enabled by the undelayed CE
            cnt_by_dly1_p : process (clk)
            begin
                if (rising_edge(clk)) then
                    if (rst = '1') then
                        cnt_by_behind_regs <= (others => '0');
                    elsif (clk_ena = '1') then
                        cnt_by_behind_regs <= cnt_by;
                    end if;
                end if;
            end process;

            -- this is the 2nd register - enabled by the once delayed CE
            cnt_by_dly2_p : process (clk)
            begin
                if (rising_edge(clk)) then
                    if (rst = '1') then
                        cnt_by_behind_all_regs <= (others => '0');
                    elsif (clk_ena_behind_regs = '1') then
                        cnt_by_behind_all_regs <= cnt_by_behind_regs;
                    end if;
                end if;
            end process;

        end generate;

    -- this is the more expected behavior
    else generate

        rst_behind_regs <= rst;

        input_regs_g : if (INPUT_REGS = false) generate

            clk_ena_behind_all_regs <= clk_ena;
            cnt_by_behind_all_regs <= cnt_by;

        else generate

            cnt_by_dly_p : process (clk)
            begin
                if (rising_edge(clk)) then
                    if (rst = '1') then
                        cnt_by_behind_all_regs <= (others => '0');
                    elsif (clk_ena = '1') then
                        cnt_by_behind_all_regs <= cnt_by;
                    end if;
                end if;
            end process;

            clk_ena_dly_g : if (DEVICE /= "STRATIX10") generate

                -- the CE here is reset
                clk_ena_dly_p : process (clk)
                begin
                    if (rising_edge(clk)) then
                        if (rst = '1') then
                            clk_ena_behind_all_regs <= '0';
                        else
                            clk_ena_behind_all_regs <= clk_ena;
                        end if;
                    end if;
                end process;

            else generate

                clk_ena_dly_p : process (clk)
                begin
                    if (rising_edge(clk)) then
                        clk_ena_behind_all_regs <= clk_ena;
                    end if;
                end process;

            end generate;

        end generate;

    end generate;

    -- the actual counter
    counting_p : process (clk)
    begin
        if (rising_edge(clk)) then
            if (rst_behind_regs = '1') then
                sim_result <= (others => '0');
            elsif (clk_ena_behind_all_regs = '1') then
                sim_result <= std_logic_vector(unsigned(sim_result) + unsigned(cnt_by_behind_all_regs));
            end if;
        end if;
    end process;

    -- ========================================================================
    -- Evaluation
    -- ========================================================================
    result_ok <= '1' when ((sim_result = cnt_result) or (correct_results = 1)) else '0';

    write_and_stop_p : process
    begin
        wait until rising_edge(clk);
        if (stop_at_the_end = '0') then
            if (result_ok = '0') then
                incorrect_results <= incorrect_results + 1;
                --if (incorrect_results mod 1000 = 0) then
                    write(l, string'("Results do not match. ")); writeline(output, l);
                    write(l, now);
                    stop(0);
                --end if;
            else
                correct_results <= correct_results + 1;
                if (correct_results mod 10000 = 0) then
                    write(l, string'(integer'image(correct_results) & " results match.")); writeline(output, l);
                end if;
            end if;
        else
            wait;
        end if;
    end process;

    -- writes out "Success." when there are no errors - needed for jenkins verification
    sim_verdict_p : process
    begin
        wait until stop_at_the_end = '1';
        if (incorrect_results = 1) then
            write(l, string'("VERIFICATION SUCCESS")); writeline(output, l);
        else
            write(l, string'(" There were some incorrect results.")); writeline(output, l);
        end if;
        wait;
    end process;

end architecture;
