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

    -- =============
    -- DUT settings
    -- =============

    -- set to true to enable input registers and increase the latency of the comparator to 2 clock cycles
    constant INPUT_REGS_EN    : boolean := false;
    -- max is now unlimited for mode ><=, others max 25 bits
    constant DATA_WIDTH       : natural := 25;
    -- set to true to use DSP blocks on Stratix 10
    constant DSP_ENABLE       : boolean := true;
    -- options: "><=", ">= ", "<= " - NOTE: the space after ">=" or "<=" is necessary
    constant MODE             : string  := "<= ";
    -- AGILEX/STRATIX10
    constant DEVICE           : string  := "AGILEX";

    -- ======================
    -- verification settings
    -- ======================

    -- set to true for more detailed reports in the Transcript window
    constant TALKATIVE        : boolean := false;
    -- writes a report about the number of correct results to the Transcript window every Nth iteration
    constant REPORT_EVERY_NTH : natural := 10000;
    -- number of clock cycles the simulation should run for
    constant LENGHT_OF_SIM    : natural := 100000;
    constant CLK_PERIOD       : time    := 10 ns;

    -- ==================================================================================
    -- constants used to calculate the number of used DSP blocks according to DATA_WIDTH
    -- ==================================================================================

    -- number of comparators that will have maximum width which is limited by the DSP block (max 25 bits wide)
    constant NUM_OF_FULL_COMPARATORS  : natural := DATA_WIDTH / 25;
    -- the rest of the bits that do not fill up the whole width of the DSP block
    constant LEFTOVER_BITS            : natural := DATA_WIDTH mod 25;
    -- munber of all used DSP blocks (fully or partially)
    constant TOTAL_NUM_OF_COMPARATORS : natural := tsel(LEFTOVER_BITS = 0, NUM_OF_FULL_COMPARATORS, NUM_OF_FULL_COMPARATORS+1);

    -- setting signals
    signal clk                     : std_logic;
    signal clk_ena                 : std_logic;
    signal rst                     : std_logic;
    signal valid                   : std_logic;
    signal valid_behind_input_regs : std_logic;
    signal valid_behind_all_regs   : std_logic; -- valid signals are used to ignore the different results from the testbench and the comparator when reset is asserted
    signal input1                  : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal input2                  : std_logic_vector(DATA_WIDTH-1 downto 0);

    -- signals for verification of a succesful run
    signal stop_at_the_end         : std_logic := '0'; -- is '1' at the end of the simulation, allows for the verdict of the simulation run to be written out
    signal clk_cycle_count         : natural := 0; -- +1 each rising edge, counts up until the LENGHT_OF_SIM is reached

    -- result of the comparator: "00" when input values are equal, "01" when the 1st is larger than the 2nd, "10" when the 2nd is larger than the 1st
    -- in modes ">=" or "<=" the result is in form of: '11' when the 1st number is larger or equal to (or smaller or equal to, respectively) the 2nd number, else '00'
    signal cmp_result             : std_logic_vector(1 downto 0);

    -- signals for the simulated comparator
    signal input1_behind_regs_uns  : unsigned(DATA_WIDTH-1 downto 0); -- input 1 for the simulated comparator in unsigned so it can be compared with input 2
    signal input2_behind_regs_uns  : unsigned(DATA_WIDTH-1 downto 0); -- input 2 for the simulated comparator in unsigned so it can be compared with input 1
    signal sim_result         : std_logic_vector(1 downto 0); -- result from the simulated comparator

    -- signals for verification of the comparator
    signal result_ok               : std_logic; -- is '1' when results from the testbench and from the comparator are equal -> the result from the comparator is correct
    signal correct_results         : natural := 1; -- counts the number of iterations when results from the testbench and from the comparator were equal; initialized to 1 to finish at the total number of iterations
    signal incorrect_results       : natural := 1; -- counts the number of iterations when results from the testbench and from the comparator were not equal; initialized to 1 to finish at the total number of iterations

    shared variable l : line;

begin

    uut : entity work.DSP_COMPARATOR_INTEL
    generic map (
        INPUT_DATA_WIDTH => DATA_WIDTH   ,
        INPUT_REGS_EN    => INPUT_REGS_EN,
        DSP_EN           => DSP_ENABLE   ,
        MODE             => MODE         ,
        DEVICE           => DEVICE
    )
    port map (
        CLK      => clk    ,
        CLK_EN   => clk_ena,
        RESET    => rst    ,
        INPUT_1  => input1 ,
        INPUT_2  => input2 ,
        RESULT   => cmp_result
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
        clk_ena_rand_gen_l : for i in 0 to LENGHT_OF_SIM loop
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
        rst_rand_gen_l : for i in 0 to LENGHT_OF_SIM loop
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

    -- generating valid signal that specifies when the comparison of cmp_result and sim_result is valid; is the opposite of rst
    valid_p : process
    begin
        if (stop_at_the_end = '0') then
            valid <= '0';
            wait until rst = '0';
            valid <= '1';
            wait until rst = '1';
        else
            wait;
        end if;
    end process;

    -- delaying the valid signal by two clock cycles if input registers are enabled, else delaying valid by one clock cycle
    valid_dly_g : if (INPUT_REGS_EN = false) generate

        final_valid_dly_p : process (clk)
        begin
            if (rising_edge(clk)) then
                if (rst = '1') then
                    valid_behind_all_regs <= '0';
                elsif (clk_ena = '1') then
                    valid_behind_all_regs <= valid;
                end if;
            end if;
        end process;

    else generate

        initial_valid_dly_p : process (clk)
        begin
            if (rising_edge(clk)) then
                if (rst = '1') then
                    valid_behind_input_regs <= '0';
                elsif (clk_ena = '1') then
                    valid_behind_input_regs <= valid;
                end if;
            end if;
        end process;

        final_valid_dly_p : process (clk)
        begin
            if (rising_edge(clk)) then
                if (rst = '1') then
                    valid_behind_all_regs <= '0';
                elsif (clk_ena = '1') then
                    valid_behind_all_regs <= valid_behind_input_regs;
                end if;
            end if;
        end process;

    end generate;

    --  ========================================================================
    --  Generating random inputs
    --  ========================================================================
    rand_input1_p : process
        variable s0 : integer := 9;
        variable s1 : integer := 6;
        variable X  : integer := 4;
    begin
        if (stop_at_the_end = '0') then
            wait until rising_edge(clk);
            -- generating random integer
            randint(s0, s1, 1, integer'high, X);
            wait for 0.1*CLK_PERIOD;
            -- using the randomly generated integer (X) to generate a random std_logic_vector
            input1 <= random_vector(DATA_WIDTH, X);
        else
            wait;
        end if;
    end process;

    rand_input2_p : process
        variable s0   : integer := 6;
        variable s1   : integer := 3;
        variable X    : integer := 7;
    begin
        if (stop_at_the_end = '0') then
            wait until rising_edge(clk);
            -- generating random integer
            randint(s0, s1, 1, integer'high, X);
            wait for 0.1*CLK_PERIOD;
            -- using the randomly generated integer (X) to generate a random std_logic_vector
            input2 <= random_vector(DATA_WIDTH, X);
        else
            wait;
        end if;
    end process;

    --  ========================================================================
    --  Simulated comparator
    --  ========================================================================
    input_regs_g : if (INPUT_REGS_EN = false) generate

        -- just renaming input signals to those that are used in the comparison logic, also converting them to unsigned, so they can be compared
        input1_behind_regs_uns <= unsigned(input1);
        input2_behind_regs_uns <= unsigned(input2);

    -- generating registers to delay input signals when input registers are enabled, also converting them to unsigned, so they can be compared
    else generate

        input1_dly_p : process (clk)
        begin
            if (rising_edge(clk)) then
                if (rst = '1') then
                    input1_behind_regs_uns <= (others => '0');
                    input2_behind_regs_uns <= (others => '0');
                elsif (clk_ena = '1') then
                    input1_behind_regs_uns <= unsigned(input1);
                    input2_behind_regs_uns <= unsigned(input2);
                end if;
            end if;
        end process;

    end generate;

    -- comparing logic
    comp_function_g : case MODE generate

        when ">= " =>

            mode1_comparing_p : process (clk)
            begin
                if (rising_edge(clk)) then
                    if (rst = '1') then
                        sim_result <= (others => '1');
                    elsif ((clk_ena = '1')) then
                        if (input1_behind_regs_uns >= input2_behind_regs_uns) then
                            sim_result <= "11";
                            if (TALKATIVE = true) then
                                write(l, string'(integer'image(to_integer(input1_behind_regs_uns)) & " >= " & integer'image(to_integer(input2_behind_regs_uns)))); writeline(output, l);
                            end if;
                        else
                            sim_result <= "00";
                            if (TALKATIVE = true) then
                                write(l, string'(integer'image(to_integer(input1_behind_regs_uns)) & " < " & integer'image(to_integer(input2_behind_regs_uns)))); writeline(output, l);
                            end if;
                        end if;
                    end if;
                end if;
            end process;

        end;

        when "<= " =>

            mode2_comparing_p : process (clk)
            begin
                if (rising_edge(clk)) then
                    if (rst = '1') then
                        sim_result <= (others => '0');
                    elsif (clk_ena = '1') then
                        if (input1_behind_regs_uns <= input2_behind_regs_uns) then
                            sim_result <= "11";
                            if (TALKATIVE = true) then
                                write(l, string'(integer'image(to_integer(input1_behind_regs_uns)) & " <= " & integer'image(to_integer(input2_behind_regs_uns)))); writeline(output, l);
                            end if;
                        else
                            sim_result <= "00";
                            if (TALKATIVE = true) then
                                write(l, string'(integer'image(to_integer(input1_behind_regs_uns)) & " > " & integer'image(to_integer(input2_behind_regs_uns)))); writeline(output, l);
                            end if;
                        end if;
                    end if;
                end if;
            end process;

        end;

        when others =>

            default_mode_comparing_p : process (clk)
            begin
                if (rising_edge(clk)) then
                    if (rst = '1') then
                        sim_result <= (others => '0');
                    elsif (clk_ena = '1') then
                        if (input1_behind_regs_uns > input2_behind_regs_uns) then
                            sim_result <= "01";
                            if (TALKATIVE = true) then
                                write(l, string'(integer'image(to_integer(input1_behind_regs_uns)) & " > " & integer'image(to_integer(input2_behind_regs_uns)))); writeline(output, l);
                            end if;
                        elsif (input2_behind_regs_uns > input1_behind_regs_uns) then
                            sim_result <= "10";
                            if (TALKATIVE = true) then
                                write(l, string'(integer'image(to_integer(input1_behind_regs_uns)) & " < " & integer'image(to_integer(input2_behind_regs_uns)))); writeline(output, l);
                            end if;
                        else
                            sim_result <= "00";
                            if (TALKATIVE = true) then
                                write(l, string'(integer'image(to_integer(input1_behind_regs_uns)) & " = " & integer'image(to_integer(input2_behind_regs_uns)))); writeline(output, l);
                            end if;
                        end if;
                    end if;
                end if;
            end process;

        end;

    end generate;

    -- comparing the result from the actual comparator with the result of the simulated comparator
    result_ok <= '1' when ((cmp_result = sim_result) or (correct_results = 1) or (valid_behind_all_regs = '0')) else '0';

    -- writing out reports about amount of iterations with correct and incorrect results to the Transcript window every Nth correct or incorrect result
    write_and_stop_p : process
    begin
        wait until rising_edge(clk);
        if (stop_at_the_end = '0') then
            if (result_ok = '0') then
                if (incorrect_results mod REPORT_EVERY_NTH = 0) then
                    write(l, string'(integer'image(incorrect_results) & " results are incorrect.")); writeline(output, l);
                    incorrect_results <= incorrect_results + 1;
                else
                    incorrect_results <= incorrect_results + 1;
                end if;
                --stop(1); -- stops the simulation after N incorrect results
            elsif (correct_results mod REPORT_EVERY_NTH = 0) then
                write(l, string'(integer'image(correct_results) & " results are correct.")); writeline(output, l);
                correct_results <= correct_results + 1;
            else
                correct_results <= correct_results + 1;
            end if;
        else
            wait;
        end if;
    end process;

    sim_verdict_p : process
    begin
        wait until stop_at_the_end = '1';
        if (incorrect_results = 1) then
            write(l, string'("VERIFICATION SUCCESS")); writeline(output, l);
        else
            write(l, string'("There were some incorrect results.")); writeline(output, l);
        end if;
        wait;
    end process;

end architecture;
