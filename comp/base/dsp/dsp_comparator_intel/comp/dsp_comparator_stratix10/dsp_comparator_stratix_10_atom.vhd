-- dsp_comparator_stratix_10_atom.vhd: It's a comparator that uses DSP blocks on Stratix 10.
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

-- NOTE: the default latency of this comparator is 2 clock cycles (with input registers enabled), to achieve latency of 1 clock cycle, disable input registers

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

library fourteennm;
use fourteennm.fourteennm_components.all;

-- NOTE: default latency of this comparator is 2 clock cycles (with input registers enabled), to achieve latency of 1 clock cycle, disable input registers

entity DSP_COMPARATOR_STRATIX_10_ATOM is
    Generic (
        -- the width of the input data; maximum width of 25 bits applies only in modes ">= " or "<= " when using DSP blocks, unlimited in other cases
        -- INPUT_DATA_WIDTH+1 is used to accomodate the sign bit
        INPUT_DATA_WIDTH : natural := 25;
        -- "0" to enable the input registers, "none" to disable them
        REG_0_EN         : boolean := true;
        -- this option allows user to choose the function of the comparator
        -- "><=" is the default mode which outputs results as specified above the RESULT port
        -- ">=" outputs result in form of '11' if the 1st number is larger or equal than the 2nd number, else '00'  - 25 is the maximum input data width !! NOTE: only one DSP block is used in this mode
        -- "<=" outputs result in form of '11' if the 1st number is smaller or equal than the 2nd number, else '00' - 25 is the maximum input data width !! NOTE: only one DSP block is used in this mode
        -- options: "><=", ">= ", "<= " - NOTE: the space after ">= " or "<= " is necessary !!
        MODE             : string  := "><="
        );
    Port (
        CLK0       :  in std_logic;
        -- enables registers
        CLK0_EN    :  in std_logic;
        -- clears registers
        RESET      :  in std_logic;
        -- the 1st number for comparison
        INPUT_1    :  in std_logic_vector(INPUT_DATA_WIDTH-1 downto 0);
        -- the 2nd number for comparison
        INPUT_2    :  in std_logic_vector(INPUT_DATA_WIDTH-1 downto 0);
        -- the output of the comparator
        -- RESULT will be "01" (1 in dec) when the 1st number (from INPUT_1) > 2nd number (from INPUT_2)
        -- RESULT will be "10" (2 in dec) when the 2nd number (from INPUT_2) > 1st number (from INPUT_1)
        -- RESULT will be "00" when both numbers are equal
        RESULT     : out std_logic_vector(1 downto 0)
    );
end entity;

architecture FULL of DSP_COMPARATOR_STRATIX_10_ATOM is

    -- this function enables the input registers in the DSP block if required (according to REG_0_EN) to be compatible with the DSP block
    function en_input_regs (REG_0_EN : boolean) return string is
    begin
        if (REG_0_EN = false) then
            -- "none" means the register does not run on any clock -> it is disabled
            return "none";
        else
            -- "0" means the register is enabled and runs on "clock 0"
            return "0";
        end if;
    end function;

    -- number of comparators that will have maximum width of 25 bits - limited by the DSP block
    constant NUM_OF_FULL_COMPARATORS  : natural := INPUT_DATA_WIDTH / 25;
    -- the rest of the bits that do not fill up the whole width of the DSP block -> less than 25 bits wide
    constant LEFTOVER_BITS            : natural := INPUT_DATA_WIDTH mod 25;
    -- number of used DSP blocks (fully or partially)
    constant TOTAL_NUM_OF_COMPARATORS : natural := tsel(LEFTOVER_BITS = 0, NUM_OF_FULL_COMPARATORS, NUM_OF_FULL_COMPARATORS+1);

    signal clr0                 : std_logic; -- this is the reset signal for input registers, is '0' when they are disabled
    signal input_1_sig          : std_logic_vector(INPUT_DATA_WIDTH downto 0); -- INPUT1 concatenated with '0' at MSB position to represent a positive number (conversion to the signed type occurs in the DSP block)
    signal input_2_sig          : std_logic_vector(INPUT_DATA_WIDTH downto 0); -- INPUT2 concatenated with '0' at MSB position to represent a positive number (conversion to the signed type occurs in the DSP block)

begin

    -- clr0 which clears the input registers must be '0' if input register are disabled, else same as RESET
    reset_for_input_regs_g : if (REG_0_EN = false) generate
        clr0 <= '0';
    else generate
        clr0 <= RESET;
    end generate;

    -- assert for wrong input data width in certain modes
    assert (((MODE = "><=") and (INPUT_DATA_WIDTH > 0)) or (((MODE = ">= ") or (MODE = "<= ")) and ((INPUT_DATA_WIDTH <= 25) and (INPUT_DATA_WIDTH > 0))))
    report "Wrong width of input data for the chosen mode or mode option is entered incorrectly." severity failure;

    dsp_comparator_function_g : case MODE generate

        when ">= " =>

            signal dout_dsp_1 : std_logic_vector(INPUT_DATA_WIDTH downto 0); -- result after subtraction in the DSP block

        begin

            -- making the input signals positive
            input_1_sig <= '0' & INPUT_1;
            input_2_sig <= '0' & INPUT_2;

            -- -----------------------------------------------------------------
            -- if input_1_sig >= input_2_sig, then input_1_sig - input_2_sig = positive number or a zero, where in both cases will MSB be '0'
            -- NOTE: using the preadder in the DSP block for the subtraction
            -- -----------------------------------------------------------------
            dsp1_i: component fourteennm_mac
            generic map (
                az_width            => INPUT_DATA_WIDTH+1,      -- width of the DSP block's input, max 26 with MSB of the input signal permanently set to '0' (max 25 useful bits)
                ay_scan_in_width    => INPUT_DATA_WIDTH+1,      -- width of the DSP block's input, max 26 with MSB of the input signal permanently set to '0' (max 25 useful bits)
                ax_width            => 1,                       -- not to be changed at any time, this is the 2nd input of the multiplier in the DSP block, must be equal to 1 (in dec)
                result_a_width      => INPUT_DATA_WIDTH+1,      -- width of the DSP block's output, MSB holds the sign bit
                operation_mode      => "m27x27",                -- mode with widest possible data inputs (and output)
                preadder_subtract_a => "true",                  -- enabling the preadder in subtraction mode
                operand_source_may  => "preadder",              -- specifies that the 1st input of the multiplier is from the preadder
                signed_may          => "true",                  -- inputs ay and az are converted to type signed, which is necessary when preadder is used in subtraction mode
                ay_scan_in_clock    => en_input_regs(REG_0_EN), -- enabling input registers when required
                az_clock            => en_input_regs(REG_0_EN), -- enabling input registers when required
                output_clock        => "0",                     -- output register runs on clock "0"
                clear_type          => "sclr"                   -- synchronous clear, NOTE: clock enable has priority over clear signal when synchronus clear is used
            )
            port map (
                clk(0)  => CLK0,
                clk(1)  => '0',              -- not used
                clk(2)  => '0',              -- not used
                ena(0)  => CLK0_EN or RESET, -- enable for clock 0, ORed with RESET because enable has the priority (registers will not reset when CLK0_EN = '0' even if RESET = '1')
                ena(1)  => '0',              -- enable for clock 1; not used
                ena(2)  => '0',              -- enable for clock 2; not used
                clr(0)  => clr0,             -- resets input registers
                clr(1)  => RESET,            -- resets output registers (and pipeline registers, which are not used)
                ay      => input_1_sig,      -- the input from which input_2_sig is subtracted
                az      => input_2_sig,      -- the input that is subtracted from input_1_sig
                ax      => (others => '1'),  -- this is the other input of the multiplier, must be 1 (in decimal) at all times so the result of subtraction stays the same
                negate  => '1',              -- inverting the result so that MSB is in the right format
                resulta => dout_dsp_1        -- dout_dsp_1 = input_1_sig - input_2_sig
            );

            -- when input_1_sig >= input_2_sig, the output is "11"
            RESULT <= dout_dsp_1(INPUT_DATA_WIDTH) & dout_dsp_1(INPUT_DATA_WIDTH);

        end;

        when "<= " =>

            signal dout_dsp_2 : std_logic_vector(INPUT_DATA_WIDTH downto 0); -- result after subtraction in the DSP block

        begin

            -- making the input signals positive
            input_1_sig <= '0' & INPUT_1;
            input_2_sig <= '0' & INPUT_2;

            -- -----------------------------------------------------------------
            -- If input_1_sig <= input_2_sig, then input_2_sig - input_1_sig = positive number or a zero, in both cases MSB will be '0'
            -- NOTE: using the preadder in the DSP block for the subtraction
            -- -----------------------------------------------------------------
            dsp2_i: component fourteennm_mac
            generic map (
                az_width            => INPUT_DATA_WIDTH+1,      -- width of the DSP block's input, max 26 with MSB of the input signal permanently set to '0' (max 25 useful bits)
                ay_scan_in_width    => INPUT_DATA_WIDTH+1,      -- width of the DSP block's input, max 26 with MSB of the input signal permanently set to '0' (max 25 useful bits)
                ax_width            => 1,                       -- not to be changed at any time, this is the 2nd input of the multiplier in the DSP block, must be equal to 1 (in dec)
                result_a_width      => INPUT_DATA_WIDTH+1,      -- width of the DSP block's output, MSB holds the sign bit
                operation_mode      => "m27x27",                -- mode with widest possible data inputs (and output)
                preadder_subtract_a => "true",                  -- enabling the preadder in subtraction mode
                operand_source_may  => "preadder",              -- specifies that the 1st input of the multiplier is from the preadder
                signed_may          => "true",                  -- inputs ay and az are converted to type signed, which is necessary when preadder is used in subtraction mode
                ay_scan_in_clock    => en_input_regs(REG_0_EN), -- enabling input registers when required
                az_clock            => en_input_regs(REG_0_EN), -- enabling input registers when required
                output_clock        => "0",                     -- output register runs on clock "0"
                clear_type          => "sclr"                   -- synchronous clear, NOTE: clock enable has priority over clear signal when synchronus clear is used
            )
            port map (
                clk(0)  => CLK0,
                clk(1)  => '0',              -- not used
                clk(2)  => '0',              -- not used
                ena(0)  => CLK0_EN or RESET, -- enable for clock 0, ORed with RESET because enable has the priority (registers will not reset when CLK0_EN = '0' even if RESET = '1')
                ena(1)  => '0',              -- enable for clock 1; not used
                ena(2)  => '0',              -- enable for clock 2; not used
                clr(0)  => clr0,             -- resets input registers
                clr(1)  => RESET,            -- resets output registers (and pipeline registers, which are not used)
                ay      => input_2_sig,      -- the input from which input_1_sig is subtracted
                az      => input_1_sig,      -- the input that is subtracted from input_2_sig
                ax      => (others => '1'),  -- this is the other input of the multiplier, must be 1 (in decimal) at all times so the result of subtraction stays the same
                negate  => '1',              -- inverting the result so that MSB is in the right format
                resulta => dout_dsp_2        -- dout_dsp_2 = input_2_sig - input_1_sig
            );

            -- when input_1_sig <= input_2_sig, the output is "11"
            RESULT <= dout_dsp_2(INPUT_DATA_WIDTH) & dout_dsp_2(INPUT_DATA_WIDTH);

        -- ---------------------------------------------------------------------
        -- this is the default mode ("><=")
        -- ---------------------------------------------------------------------
        when others =>

            signal dout_dsp_1           : std_logic_vector(NUM_OF_FULL_COMPARATORS*26-1 downto 0); -- output of all DSP blocks that use max width of inputs (26 bits)
            signal dout_dsp_2           : std_logic_vector(NUM_OF_FULL_COMPARATORS*26-1 downto 0); -- output of all DSP blocks that use max width of inputs (26 bits)
            signal input_1_sig_leftover : std_logic_vector(LEFTOVER_BITS downto 0); -- signal that accomodates the bits that do not fill up the whole DSP block (<26 bits)
            signal input_2_sig_leftover : std_logic_vector(LEFTOVER_BITS downto 0); -- signal that accomodates the bits that do not fill up the whole DSP block (<26 bits)
            signal dout_dsp_1_leftover  : std_logic_vector(LEFTOVER_BITS downto 0); -- output of the 1st DSP block where input_2_sig_leftover is subtracted from input_1_sig_leftover
            signal dout_dsp_2_leftover  : std_logic_vector(LEFTOVER_BITS downto 0); -- output of the 2nd DSP block where input_1_sig_leftover is subtracted from input_2_sig_leftover
            signal combined_result      : slv_array_t(TOTAL_NUM_OF_COMPARATORS-1 downto 0)(1 downto 0); -- array of results from each comparator (from each pair of DSP blocks that form one comparator)

        begin

            comparators_g : for i in NUM_OF_FULL_COMPARATORS downto 1 generate

                -- -------------------------------------------------------------
                -- the 1st DSP block where the input values are converted to signed and subtracted, the output (resulta) is back in type std_logic_vector
                -- -------------------------------------------------------------
                dsp1_i: component fourteennm_mac
                generic map (
                    az_width            => 26,                      -- 26 is the max width a single DSP block can have in preadder subtraction mode
                    ay_scan_in_width    => 26,                      -- 26 is the max width a single DSP block can have in preadder subtraction mode
                    ax_width            => 1,                       -- not to be changed at any time, this is the 2nd input of the multiplier in the DSP block, must be equal to 1 (in dec)
                    result_a_width      => 26,                      -- width of the DSP block's output, MSB holds the sign bit
                    operation_mode      => "m27x27",                -- mode with widest possible data inputs (and output)
                    preadder_subtract_a => "true",                  -- enabling the preadder in subtraction mode
                    operand_source_may  => "preadder",              -- specifies that the 1st input of the multiplier is from the preadder
                    signed_may          => "true",                  -- inputs ay and az are converted to type signed, which is necessary when preadder is used in subtraction mode
                    ay_scan_in_clock    => en_input_regs(REG_0_EN), -- enabling input registers when required
                    az_clock            => en_input_regs(REG_0_EN), -- enabling input registers when required
                    output_clock        => "0",                     -- output register runs on clock "0"
                    clear_type          => "sclr"                   -- synchronous clear, NOTE: clock enable has priority over clear signal when synchronus clear is used
                )
                port map (
                    clk(0)  => CLK0,
                    clk(1)  => '0',              -- not used
                    clk(2)  => '0',              -- not used
                    ena(0)  => CLK0_EN or RESET, -- enable for clock 0, ORed with RESET because enable has the priority (registers will not reset when CLK0_EN = '0' even if RESET = '1')
                    ena(1)  => '0',              -- enable for clock 1; not used
                    ena(2)  => '0',              -- enable for clock 2; not used
                    clr(0)  => clr0,             -- resets input registers
                    clr(1)  => RESET,            -- resets output registers (and pipeline registers, which are not used)
                    ay      => '0' & INPUT_1(i*25-1 downto (i-1)*25), -- the input from which cerain part of INPUT_2 is subtracted
                    az      => '0' & INPUT_2(i*25-1 downto (i-1)*25), -- the input that is subtracted from INPUT_1
                    ax      => (others => '1'),                       -- this is the other input of the multiplier, must be 1 (in decimal) at all times so the result of subtraction stays the same
                    resulta => dout_dsp_1(i*26-1 downto (i-1)*26)     -- dout_dsp_1 = INPUT_1 - INPUT_2
                );

                -- -------------------------------------------------------------
                -- The 2nd DSP block where the input values are converted to signed and subtracted in reversed order than in the 1st DSP block, the output (resulta) is back in type std_logic_vector
                -- -------------------------------------------------------------
                dsp2_i: component fourteennm_mac
                generic map (
                    az_width            => 26,                      -- 26 is the max width a single DSP block can have in preadder subtraction mode
                    ay_scan_in_width    => 26,                      -- 26 is the max width a single DSP block can have in preadder subtraction mode
                    ax_width            => 1,                       -- not to be changed at any time, this is the 2nd input of the multiplier in the DSP block, must be equal to 1 (in dec)
                    result_a_width      => 26,                      -- width of the DSP block's output, MSB holds the sign bit
                    operation_mode      => "m27x27",                -- mode with widest possible data inputs (and output)
                    preadder_subtract_a => "true",                  -- enabling the preadder in subtraction mode
                    operand_source_may  => "preadder",              -- specifies that the 1st input of the multiplier is from the preadder
                    signed_may          => "true",                  -- inputs ay and az are converted to type signed, which is necessary when preadder is used in subtraction mode
                    ay_scan_in_clock    => en_input_regs(REG_0_EN), -- enabling input registers when required
                    az_clock            => en_input_regs(REG_0_EN), -- enabling input registers when required
                    output_clock        => "0",                     -- output register runs on clock "0"
                    clear_type          => "sclr"                   -- synchronous clear, NOTE: clock enable has priority over clear signal when synchronus clear is used
                )
                port map (
                    clk(0)  => CLK0,
                    clk(1)  => '0',              -- not used
                    clk(2)  => '0',              -- not used
                    ena(0)  => CLK0_EN or RESET, -- enable for clock 0, ORed with RESET because enable has the priority (registers will not reset when CLK0_EN = '0' even if RESET = '1')
                    ena(1)  => '0',              -- enable for clock 1; not used
                    ena(2)  => '0',              -- enable for clock 2; not used
                    clr(0)  => clr0,             -- resets input registers
                    clr(1)  => RESET,            -- resets output registers (and pipeline registers, which are not used)
                    ay      => '0' & INPUT_2(i*25-1 downto (i-1)*25), -- the input from which INPUT_1 is subtracted
                    az      => '0' & INPUT_1(i*25-1 downto (i-1)*25), -- the input that is subtracted from INPUT_2
                    ax      => (others => '1'),                       -- this is the other input of the multiplier, must be 1 (in decimal) at all times so the result of subtraction stays the same
                    resulta => dout_dsp_2(i*26-1 downto (i-1)*26)     -- dout_dsp_2 = INPUT_2 - INPUT_1
                );

                -- results from each comparator are stored in this array - comparison of higher bits is at thigher position of the array
                -- each field of the array contains the result of according comparator in a form specified above the RESULT port
                -- when the 1st number is larger than the 2nd, the MSB of the dout_dsp_1 signal is '0' (as it is a positive number)
                -- while the MSB of the dout_dsp_2 signal is '1' (as it is a negative number) and vice versa; when they are equal, both MSBs are '0'
                combined_result(i-1) <= dout_dsp_1(i*26-1) & dout_dsp_2(i*26-1);

            end generate;

            -- the comparator of leftover bits is generated only when there are some leftover bits to be compared
            comparator_of_leftover_bits_g : if (LEFTOVER_BITS /= 0) generate

                -- making the input signals positive
                input_1_sig_leftover <= '0' & INPUT_1(INPUT_DATA_WIDTH-1 downto NUM_OF_FULL_COMPARATORS*25);
                input_2_sig_leftover <= '0' & INPUT_2(INPUT_DATA_WIDTH-1 downto NUM_OF_FULL_COMPARATORS*25);

                -- -------------------------------------------------------------
                -- The 1st DSP block where the input values are converted to signed and subtracted, the output (resulta) is back in type std_logic_vector
                -- -------------------------------------------------------------
                dsp1_i: component fourteennm_mac
                generic map (
                    az_width            => LEFTOVER_BITS+1,         -- is as wide it needs to be to accomodate the rest of the bits that did not make it into a full comparator
                    ay_scan_in_width    => LEFTOVER_BITS+1,         -- is as wide it needs to be to accomodate the rest of the bits that did not make it into a full comparator
                    ax_width            => 1,                       -- not to be changed at any time, this is the 2nd input of the multiplier in the DSP block, must be equal to 1 (in dec)
                    result_a_width      => LEFTOVER_BITS+1,         -- is as wide it needs to be to accomodate the rest of the bits, MSB holds the sign bit
                    operation_mode      => "m27x27",                -- mode with widest possible data inputs (and output)
                    preadder_subtract_a => "true",                  -- enabling the preadder in subtraction mode
                    operand_source_may  => "preadder",              -- specifies that the 1st input of the multiplier is from the preadder
                    signed_may          => "true",                  -- inputs ay and az are converted to type signed, which is necessary when preadder is used for subtraction
                    ay_scan_in_clock    => en_input_regs(REG_0_EN), -- enabling input registers when required
                    az_clock            => en_input_regs(REG_0_EN), -- enabling input registers when required
                    output_clock        => "0",                     -- output register runs on clock "0"
                    clear_type          => "sclr"                   -- synchronous clear, NOTE: clock enable has priority over clear signal when synchronus clear is used
                )
                port map (
                    clk(0)  => CLK0,
                    clk(1)  => '0',                  -- not used
                    clk(2)  => '0',                  -- not used
                    ena(0)  => CLK0_EN or RESET,     -- enable for clock 0, ORed with RESET because enable has the priority (registers will not reset when CLK0_EN = '0' even if RESET = '1')
                    ena(1)  => '0',                  -- enable for clock 1; not used
                    ena(2)  => '0',                  -- enable for clock 2; not used
                    clr(0)  => clr0,                 -- resets input registers
                    clr(1)  => RESET,                -- resets output registers (and pipeline registers, which are not used)
                    ay      => input_1_sig_leftover, -- the input from which input_2_sig_leftover is subtracted
                    az      => input_2_sig_leftover, -- the input that is subtracted from input_1_sig_leftover
                    ax      => (others => '1'),      -- this is the other input of the multiplier, must be 1 (in decimal) at all times so the result of subtraction stays the same
                    resulta => dout_dsp_1_leftover   -- dout_dsp_1_leftover = input_1_sig_leftover - input_2_sig_leftover
                );

                -- -------------------------------------------------------------
                -- The 2nd DSP block where the input values are converted to signed and subtracted in reversed order than in the 1st DSP block; the output (resulta) is back in type std_logic_vector
                -- -------------------------------------------------------------
                dsp2_i: component fourteennm_mac
                generic map (
                    az_width            => LEFTOVER_BITS+1,         -- is as wide it needs to be to accomodate the rest of the bits that did not make it into a full comparator
                    ay_scan_in_width    => LEFTOVER_BITS+1,         -- is as wide it needs to be to accomodate the rest of the bits that did not make it into a full comparator
                    ax_width            => 1,                       -- not to be changed at any time, this is the 2nd input of the multiplier in the DSP block, must be equal to 1 (in dec)
                    result_a_width      => LEFTOVER_BITS+1,         -- is as wide it needs to be to accomodate the rest of the bits, MSB holds the sign bit
                    operation_mode      => "m27x27",                -- mode with widest possible data inputs and outputs
                    preadder_subtract_a => "true",                  -- enabling the preadder
                    operand_source_may  => "preadder",              -- specifies that the 1st input of the multiplier is from the preadder
                    signed_may          => "true",                  -- inputs ay and az are converted to type signed, which is necessary when preadder is used for subtraction
                    ay_scan_in_clock    => en_input_regs(REG_0_EN), -- enabling input registers when required
                    az_clock            => en_input_regs(REG_0_EN), -- enabling input registers when required
                    output_clock        => "0",                     -- output register runs on clock "0"
                    clear_type          => "sclr"                   -- synchronous clear, NOTE: clock enable has priority over clear signal when synchronus clear is used
                )
                port map (
                    clk(0)  => CLK0,
                    clk(1)  => '0',                  -- not used
                    clk(2)  => '0',                  -- not used
                    ena(0)  => CLK0_EN or RESET,     -- enable for clock 0, ORed with RESET because enable has the priority (registers will not reset when CLK0_EN = '0' even if RESET = '1')
                    ena(1)  => '0',                  -- enable for clock 1; not used
                    ena(2)  => '0',                  -- enable for clock 2; not used
                    clr(0)  => clr0,                 -- resets input registers
                    clr(1)  => RESET,                -- resets output registers (and pipeline registers, which are not used)
                    ay      => input_2_sig_leftover, -- the input from which input_1_sig_leftover is subtracted
                    az      => input_1_sig_leftover, -- the input that is subtracted from input_2_sig_leftover
                    ax      => (others => '1'),      -- this is the other input of the multiplier, must be 1 (in decimal) at all times so the result of subtraction stays the same
                    resulta => dout_dsp_2_leftover   -- dout_dsp_2_leftover = input_2_sig_leftover - input_1_sig_leftover
                );

                -- the leftover bits are at the highest position of the inputs, so the result of their comaprison is at the highest position in this array of results from all comparators
                -- each field of the array contains the result of according comparator in a form specified above the RESULT port
                -- when the 1st number is larger than the 2nd, the MSB of the dout_dsp_1_leftover signal is '0' (as it is a positive number)
                -- while the MSB of the dout_dsp_2_leftover signal is '1' (as it is a negative number) and vice versa; when they are equal, both MSBs are '0'
                combined_result(TOTAL_NUM_OF_COMPARATORS-1) <= dout_dsp_1_leftover(LEFTOVER_BITS) & dout_dsp_2_leftover(LEFTOVER_BITS);

            end generate;

            -- this process chooses one of the results from the partial comparators to be the final result of the whole comparator
            final_result_p : process (all)
            begin
                -- inputs are equal when results of all partial comparators are equal
                RESULT <= "00";
                -- this loop searches for the first inequation of the partial results, because the first inequation defines the result of the whole comparison
                final_result_l : for i in TOTAL_NUM_OF_COMPARATORS-1 downto 0 loop
                    if (combined_result(i) /= "00") then
                        RESULT <= combined_result(i);
                        exit;
                    end if;
                end loop;
            end process;

        end;

    end generate;

end architecture;
