-- dsp_counter_intel_ent.vhd:
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

entity DSP_COUNTER_INTEL is
    Generic (
        -- AUTO_RESET lets the user to specify what happens when the counter reaches its maximum value
        -- with AUTO_RESET set to false the counter stops counting and hold: its MAXIMUM value when the MAX_VAL is reached (MAX_VAL must be set to (others => '1'))
        --                                                                   its MINIMUM value when the MAX_VAL is reached (MAX_VAL must be set to (others => '0'))
        AUTO_RESET     : boolean := true;
        -- enable input registers, then the latency will be 2 clock cycles
        INPUT_REGS     : boolean := true;
        -- the width of counter input (max 27 when DSPs are used)
        COUNT_BY_WIDTH : natural := 27;
        -- the width of counter output (max 64 when DSPs are used)
        RESULT_WIDTH   : natural := 64;
        -- set to true to use DSP block for the counter
        DSP_ENABLE     : boolean := true;
        -- if true, the counter subtracts the count_by signal from the current result (it counts down)
        COUNT_DOWN     : boolean := false;
        -- target FPGA: "AGILEX" or "STRATIX10"
        DEVICE         : string  := "AGILEX"
        );
    Port (
        -- the source for clock 0 and clock 1, further explained in DSP_COUNTER_STRATIX_10_ATOM
        CLK      :  in std_logic;
        -- enables all registers
        CLK_EN   :  in std_logic;
        -- resets all registers
        RESET    :  in std_logic;
        -- counter counts up or down by this number (the counter input)
        COUNT_BY :  in std_logic_vector(COUNT_BY_WIDTH-1 downto 0);
        -- MAX_VAL is the maximum (or minimum) value the counter can reach - only important when AUTO_RESET = false;
        -- expected to be (others => '1') when counting up and (others => '0') when counting down;
        -- other values are not supported and the counter will most likely malfunction
        MAX_VAL  :  in std_logic_vector(RESULT_WIDTH-1 downto 0) := (others => '1');
        -- the output of the counter
        RESULT   : out std_logic_vector(RESULT_WIDTH-1 downto 0)
    );
end entity;
