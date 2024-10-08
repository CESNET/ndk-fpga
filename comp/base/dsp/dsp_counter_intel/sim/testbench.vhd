-- testbench.vhd.
-- Copyright (C) 2020 CESNET z. s. p. o.
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

--! ----------------------------------------------------------------------------
--!                        Entity declaration
--! ----------------------------------------------------------------------------
entity TESTBENCH is
end entity TESTBENCH;
--! ----------------------------------------------------------------------------
--!                      Architecture declaration
--! ----------------------------------------------------------------------------
architecture BEHAVIORAL of TESTBENCH is

    -- =====================
    -- DUT settings
    -- =====================

    constant AUTO_RESET       : boolean := false;
    constant INPUT_REGS       : boolean := false;
    -- max 27
    constant COUNT_BY_WIDTH   : natural := 27;
    -- max 64
    constant RESULT_WIDTH     : natural := 64;
    constant DSP_ENABLE       : boolean := false;
    -- the counter counts down when set to true
    constant COUNT_DOWN       : boolean := true;
    -- "AGILEX" or "STRATIX10"
    constant DEVICE           : string  := "AGILEX";

    -- =====================
    -- verification settings
    -- =====================

    -- write report in the Transcript window about the number correct results every N-th transaction
    constant REPORT_EVERY_NTH : natural := 1000;
    -- number of clock cycles the simulation should run for - this must concur with the length of simulation defined in sim_sig.fdo ("run ... us")
    constant LENGHT_OF_SIM    : natural := 50000;
    constant CLK_PERIOD       : time    := 10 ns;

    -- used to set the value of max signal that will be used in the simulation, at this time, only 2 values of max are possible
    function get_max_f(down : boolean; out_width : natural) return std_logic_vector is
    begin
        if (down = true) then
            return (out_width-1 downto 0 => '0');
        else
            return (out_width-1 downto 0 => '1');
        end if;
    end function;

    -- setting signals
    signal clk                 : std_logic;
    signal clk_ena             : std_logic;
    signal rst                 : std_logic;
    signal cnt_by              : std_logic_vector(COUNT_BY_WIDTH-1 downto 0); -- the value of the counter is incremented or decremented by this number
    signal max                 : std_logic_vector(RESULT_WIDTH-1 downto 0) := get_max_f(COUNT_DOWN, RESULT_WIDTH); -- counter's maximum or minimum (depending on COUNT_DOWN)

    signal cnt_result          : std_logic_vector(RESULT_WIDTH-1 downto 0); -- the value from the counter (component)

    -- other signals
    signal clk_cycle_count     : natural := 0; -- counts for how many clock cycles this simulation has run
    signal stop_at_the_end     : std_logic := '0'; -- stops the simulation when LENGHT_OF_SIM is reached
    signal cnt_by_behind_regs  : std_logic_vector(COUNT_BY_WIDTH-1 downto 0); -- if input register is enabled, cnt_by signal is delayed, else is just renamed
    signal clk_ena_behind_regs : std_logic; -- if input register is enabled, clk_ena signal is delayed, else is just renamed
    signal incorrect_results   : natural := 1; -- counts the number of incorrect results (results from the counter that match results from the testbench)

    -- final signals
    signal sim_result          : std_logic_vector(RESULT_WIDTH-1 downto 0); --  result of the simulated counter; to be compared with the result of the real counter (cnt_result)
    signal correct_results     : natural := 1; -- counts the number of correct results (results from the counter that match results from the testbench)
    signal result_ok           : std_logic; -- indicates whether the current result from the counter matches the current result from the testbench

    shared variable l : line; -- is used to write lines of text into the Transcript window

begin
    uut : entity work.DSP_COUNTER_INTEL
    generic map (
        AUTO_RESET     => AUTO_RESET,
        INPUT_REGS     => INPUT_REGS,
        COUNT_BY_WIDTH => COUNT_BY_WIDTH,
        RESULT_WIDTH   => RESULT_WIDTH,
        DSP_ENABLE     => DSP_ENABLE,
        COUNT_DOWN     => COUNT_DOWN,
        DEVICE         => DEVICE
    )
    port map(
        CLK        => clk,
        CLK_EN     => clk_ena,
        RESET      => rst,
        COUNT_BY   => cnt_by,
        MAX_VAL    => max,
        RESULT     => cnt_result
    );

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
        variable s1 : integer := 7;
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
        variable s1 : integer := 4;
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
        variable s0 : integer := 6;
        variable s1 : integer := 9;
        variable X  : integer := 4;
    begin
        if (stop_at_the_end = '0') then
            wait until rising_edge(clk);
            -- generating random integer
            randint(s0, s1, 1, integer'high, X);
            wait for 0.1*CLK_PERIOD;
            -- using the randomly generated integer (X) to generate a random std_logic_vector
            cnt_by <= random_vector(COUNT_BY_WIDTH, X);
        else
            wait;
        end if;
    end process;

    -- ----------------------------------------------------------------------------------------------
    -- this is the simulated counter, whose result is compared with the result from the tested counter
    -- ----------------------------------------------------------------------------------------------
    -- renaming the clk_ena signal, also delaying it if input registers are enabled
    clk_ena_behind_regs_g : if (INPUT_REGS = false) generate
        clk_ena_behind_regs <= clk_ena;
    else generate
        clk_ena_dly_p : process (clk)
        begin
            if (rising_edge(clk)) then
                if (rst = '1') then
                    clk_ena_behind_regs <= '0';
                else
                    clk_ena_behind_regs <= clk_ena;
                end if;
            end if;
        end process;
    end generate;

    -- renaming the cnt_by signal, also delaying it if input registers are enabled
    cnt_by_behind_regs_g : if (INPUT_REGS = false) generate
        cnt_by_behind_regs  <= cnt_by;
    else generate
        cnt_by_dly_p : process (clk)
        begin
            if (rising_edge(clk)) then
                if (rst = '1') then
                    cnt_by_behind_regs <= (others => '0');
                elsif (clk_ena = '1') then
                    cnt_by_behind_regs  <= cnt_by;
                end if;
            end if;
        end process;
    end generate;

    -- when AUTO_RESET is true the counter naturally overflows/underflows
    autoreset_g : if (AUTO_RESET = true) generate

        count_up_or_down_p : process (clk)
        begin
            if (rising_edge(clk)) then
                if (rst = '1') then
                    sim_result <= (others => '0');
                elsif (clk_ena_behind_regs = '1') then
                    if (COUNT_DOWN = true) then
                        sim_result <= std_logic_vector(unsigned(sim_result) - unsigned(cnt_by_behind_regs));
                    else
                        sim_result <= std_logic_vector(unsigned(sim_result) + unsigned(cnt_by_behind_regs));
                    end if;
                end if;
            end if;
        end process;

    -- AUTO_RESET is false, the counter keeps max at the output
    else generate

        signal sim_result_ext2 : unsigned(RESULT_WIDTH+1 downto 0); -- signal sim_result etended by 2 bits
        signal freeze_at_max   : std_logic; -- this signal stops (freezes) the counter just as it is about to overflow/underflow

    begin

        count_up_or_down_g : if (COUNT_DOWN = true) generate

            signal cnt_by_behind_regs_ext : std_logic_vector(COUNT_BY_WIDTH downto 0); -- signal cnt_by_behind_regs extended by 1 bit

        begin

            -- concatenated with MSB = '0' so it will be always a positive number when converted to signed
            cnt_by_behind_regs_ext <= '0' & cnt_by_behind_regs;

            counting_down_p : process (clk)
            begin
                if (rising_edge(clk)) then
                    if (rst = '1') then
                        sim_result_ext2 <= (others => '0');
                        -- the 1st bit is '0' because it must be a positive number after conversion to type signed
                        -- the 2nd bit is '1' to surpass initial overflow that happens with the 1st subtraction after a reset
                        sim_result_ext2(RESULT_WIDTH+1 downto RESULT_WIDTH) <= "01";
                        freeze_at_max <= '0';
                    elsif ((clk_ena_behind_regs = '1') and (freeze_at_max = '0')) then
                        if (signed(sim_result_ext2) - signed(cnt_by_behind_regs_ext) >= 0) then
                            sim_result_ext2 <= sim_result_ext2 - unsigned(cnt_by_behind_regs_ext);
                        else
                            freeze_at_max <= '1';
                        end if;
                    end if;
                end if;
            end process;

        -- when counting up
        else generate

            counting_up_p : process (clk)
            begin
                if (rising_edge(clk)) then
                    if (rst = '1') then
                        sim_result_ext2 <= (others => '0');
                        freeze_at_max <= '0';
                    elsif ((clk_ena_behind_regs = '1') and (freeze_at_max = '0')) then
                        if (sim_result_ext2 + unsigned(cnt_by_behind_regs) <= unsigned(max)) then
                            sim_result_ext2 <= sim_result_ext2 + unsigned(cnt_by_behind_regs);
                        else
                            freeze_at_max <= '1';
                        end if;
                    end if;
                end if;
            end process;

        end generate;

        -- assigning only necessary bits of the sim_result_ext2 signal or max when underflow is detected
        sim_result <= std_logic_vector(sim_result_ext2(RESULT_WIDTH-1 downto 0)) when (freeze_at_max = '0') else max;


    end generate;

    -- comparing the result from the counter with the result from the simulated counter - the 1st clock cycle is ignored
    result_ok <= '1' when ((sim_result = cnt_result) or (clk_cycle_count = 0)) else '0';

    -- -------------------------------------------------------------------------
    -- printing out report about the success of the simulation
    -- -------------------------------------------------------------------------
    write_and_stop_p : process
    begin
        wait until rising_edge(clk);
        if (stop_at_the_end = '0') then
            if (result_ok = '0') then
                incorrect_results <= incorrect_results + 1;
                if (incorrect_results mod REPORT_EVERY_NTH = 0) then
                    write(l, string'(integer'image(incorrect_results) & " results do not match. ")); writeline(output, l);
                    stop(1);
                end if;
            else
                correct_results <= correct_results + 1;
                if (correct_results mod REPORT_EVERY_NTH = 0) then
                    write(l, string'("Results match. Iteration: " & integer'image(correct_results))); writeline(output, l);
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
