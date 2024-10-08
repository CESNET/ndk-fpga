-- dsp_comparator_intel.vhd: It's a comparator that can use DSP blocks on Stratix 10 or Agilex or common logic.
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

architecture FULL of DSP_COMPARATOR_INTEL is

    -- signals for non DSP counter
    signal input1_behind_regs : std_logic_vector(INPUT_DATA_WIDTH-1 downto 0) := (others => '0'); -- renamed input1 signal and delayed one clock cycle when input registers are enabled
    signal input2_behind_regs : std_logic_vector(INPUT_DATA_WIDTH-1 downto 0) := (others => '0'); -- renamed input2 signal and delayed one clock cycle when input registers are enabled
    signal early_result       : std_logic_vector(1 downto 0); -- the result after comparison; "early" because it needs to be delayed one clock cycle to match the the specified latency

begin

    -- using general logic for the comparator when DSP blocks are disabled
    dsp_enable_g : if (DSP_EN = false) generate

        -- only connecting signals to corresponding ports when input registers are disabled
        input_regs_g : if (INPUT_REGS_EN = false) generate

            input1_behind_regs <= INPUT_1;
            input2_behind_regs <= INPUT_2;

        -- generating registers for the input signals when input registers are enabled
        else generate

            input1_dly_p : process (CLK)
            begin
                if (rising_edge(clk)) then
                    if (RESET = '1') then
                        input1_behind_regs <= (others => '0');
                        input2_behind_regs <= (others => '0');
                    elsif (CLK_EN = '1') then
                        input1_behind_regs <= INPUT_1;
                        input2_behind_regs <= INPUT_2;
                    end if;
                end if;
            end process;

        end generate;

        -- comparator logic
        mode1_g : if (MODE = ">= ") generate
            early_result <= "11" when (input1_behind_regs >= input2_behind_regs) else "00";
        end generate;
        mode2_g : if (MODE = "<= ") generate
            early_result <= "11" when (input1_behind_regs <= input2_behind_regs) else "00";
        end generate;
        def_mode_g : if (MODE = "><=") generate
            early_result(0) <= '1' when (input1_behind_regs > input2_behind_regs) else '0';
            early_result(1) <= '1' when (input1_behind_regs < input2_behind_regs) else '0';
        end generate;

        -- delaying the result of the comparison to match the specified latency
        early_result_dly_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    RESULT <= (others => '0');
                elsif (CLK_EN = '1') then
                    RESULT <= early_result;
                end if;
            end if;
        end process;

    -- when DSP blocks are used for the comparator
    else generate

        device_g : if (DEVICE = "STRATIX10") generate

            dsp_i: entity work.DSP_COMPARATOR_STRATIX_10_ATOM
            generic map (
                INPUT_DATA_WIDTH => INPUT_DATA_WIDTH,
                REG_0_EN         => INPUT_REGS_EN,
                MODE             => MODE
            )
            port map (
                CLK0    => CLK,
                CLK0_EN => CLK_EN or RESET, -- CLK_EN has to be ORed with RESET, because enable has the priority (registers will not reset when CLK_EN = '0' even if RESET = '1')
                RESET   => RESET,
                INPUT_1 => INPUT_1,
                INPUT_2 => INPUT_2,
                RESULT  => RESULT
            );

        -- if DEVICE is "AGILEX"
        else generate

            dsp_i: entity work.DSP_COMPARATOR_AGILEX_ATOM
            generic map (
                INPUT_DATA_WIDTH => INPUT_DATA_WIDTH,
                REG_0_EN         => INPUT_REGS_EN,
                MODE             => MODE
            )
            port map (
                CLK     => CLK,
                CLK_EN  => CLK_EN or RESET, -- CLK_EN has to be ORed with RESET, because enable has the priority (registers will not reset when CLK_EN = '0' even if RESET = '1')
                RESET   => RESET,
                INPUT_1 => INPUT_1,
                INPUT_2 => INPUT_2,
                RESULT  => RESULT
            );

        end generate;



    end generate;

end architecture;
