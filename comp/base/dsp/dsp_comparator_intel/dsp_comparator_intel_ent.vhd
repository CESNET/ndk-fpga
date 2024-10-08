-- dsp_comparator_intel_ent.vhd:
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- NOTE: the default latency of this comparator is 2 clock cycles (with input registers enabled), to achieve latency of 1 clock cycle, disable input registers

entity DSP_COMPARATOR_INTEL is
    Generic (
        -- the width of input; maximum width of 25 bits applies only in modes ">= " or "<= " when using DSP blocks, unlimited in other cases
        INPUT_DATA_WIDTH : natural := 25;
        -- enable input registers
        INPUT_REGS_EN    : boolean := true;
        -- set to true to use DSP blocks for the comparator on Stratix 10
        DSP_EN           : boolean := true;
        -- this option allows user to choose the function of the comparator
        -- "><=" is the default mode which outputs results as specified above the RESULT port
        -- ">= " outputs result in form of '11' if the 1st number is larger or equal than the 2nd number, else '00'  - in this mode, only one DSP block is used (when enabled)
        -- "<= " outputs result in form of '11' if the 1st number is smaller or equal than the 2nd number, else '00' - in this mode, only one DSP block is used (when enabled)
        -- options: "><=", ">= ", "<= " - NOTE: the space after ">=" or "<=" is necessary !!
        MODE             : string  := "><=";
        -- "AGILEX" or "STRATIX10"
        DEVICE           : string  := "AGILEX"
        );
    Port (
        CLK     :  in std_logic;
        CLK_EN  :  in std_logic;
        RESET   :  in std_logic;
        -- the 1st number for comparison
        INPUT_1 :  in std_logic_vector(INPUT_DATA_WIDTH-1 downto 0);
        -- the 2nd number for comparison
        INPUT_2 :  in std_logic_vector(INPUT_DATA_WIDTH-1 downto 0);
        -- the final value of the comparator
        -- RESULT will be: "01" (1 in dec) when the 1st number (from INPUT_1) > 2nd number (from INPUT_2) - applies only for mode "><="
        --                 "10" (2 in dec) when the 2nd number (from INPUT_2) > 1st number (from INPUT_1) - applies only for mode "><="
        --                 "00" when both numbers are equal                                               - applies only for mode "><="
        RESULT  : out std_logic_vector(1 downto 0)
    );
end entity;
