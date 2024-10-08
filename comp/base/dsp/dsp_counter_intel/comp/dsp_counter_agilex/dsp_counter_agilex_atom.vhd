-- dsp_counter_stratix_10_atom.vhd: It's a DSP block configured as a counter.
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

library tennm;
use tennm.tennm_components.all;

entity DSP_COUNTER_AGILEX_ATOM is
    Generic (
        -- the width of counter input (max 27)
        COUNT_BY_WIDTH  : natural   := 27;
        -- the width of counter output (max 64)
        RESULT_WIDTH    : natural   := 64;
        -- if deasserted (default), the counter adds the count_by signal and the current result (it counts up)
        -- if asserted, the counter subtracts the count_by signal from the current result (it counts down); right now it counts down from 0, so it immediately underflows
        COUNT_DOWN      : std_logic := '0';
        -- set to "0" to use input registers - they will be eanbled by CLK_EN0, set to "none" to bypass them
        REG_0_EN        : boolean   := true
        );
    Port (
        -- clock
        CLK        :  in std_logic;
        -- enables input registers (if used)
        CLK_EN0    :  in std_logic;
        -- enables output registers
        CLK_EN1    :  in std_logic;
        -- clears all registers
        RESET      :  in std_logic;
        -- counter counts up or down by this number
        COUNT_BY   :  in std_logic_vector(COUNT_BY_WIDTH-1 downto 0);
        -- the output value of the counter
        RESULT     : out std_logic_vector(RESULT_WIDTH-1 downto 0)
    );
end entity;

architecture STRUCT of DSP_COUNTER_AGILEX_ATOM is

    signal clr0 : std_logic; -- input registers do not reset when they are disabled

    -- this function enables the input register in the DSP counter according to generic INPUT_REGS
    function input_reg_0_en (REG_0_EN : boolean) return string is
    begin
        if (REG_0_EN = false) then
            return "no_reg";
        else
            return "0"; -- "0" means the register is enabled by ena(0)
        end if;
    end function;

begin

    assert ((COUNT_BY_WIDTH <= 27) and (RESULT_WIDTH <= 64))
    report "Incorrect input or output width." severity failure;

    -- the reset signal is passed down to the input registers only when they are enabled
    reset_for_input_registers_g : if (REG_0_EN = false) generate
        clr0 <= '0';
    else generate
        clr0 <= RESET;
    end generate;

    dsp_i: component tennm_mac
	generic map (
            ax_width         => 1,                        -- the value is always 1, so signal ax is 1-bit wide and by assigning value (others => '1') it then has value of 1 in dec
            ay_scan_in_width => COUNT_BY_WIDTH,           -- input width
            result_a_width   => RESULT_WIDTH,
            operation_mode   => "m27x27",                 -- mode with inputs up to 27 bits wide
            ay_scan_in_clken => input_reg_0_en(REG_0_EN), -- input registers are enabled by ena(0) if input registers are enabled
            ax_clken         => input_reg_0_en(REG_0_EN), -- even constant input must be driven through register if input registers are enabled
            output_clken     => "1",                      -- output registers are enabled by ena(1)
            clear_type       => "sclr"                    -- synchronous clear (reset)
        )
        port map (
            clk              => CLK,
            ena(0)           => CLK_EN0 or RESET, -- enable for chosen registers (in this case, input registers as stated in generic map)
            ena(1)           => CLK_EN1 or RESET, -- enable for chosen registers (in this case, output registers as stated in generic map)
            ena(2)           => '0',              -- this enable is not used
            clr(0)           => clr0,             -- resets input registers
            clr(1)           => RESET,            -- resets output registers (and pipeline registers, which are not used here)
            accumulate       => '1',              -- always '1' in the counter arrangement
            negate           => COUNT_DOWN,       -- option to count down (it makes 2's complement of the COUNT_BY signal)
            ay               => COUNT_BY,         -- increment (or decrement) by this value
            ax               => (others => '1'),  -- this is the other input of the multiplier, must be always 1 else the counter will incerment by the input data multiplied by this number
            cy               => (others => '0'),
            cx               => (others => '0'),
            dy               => (others => '0'),
            dx               => (others => '0'),
            disable_scanin   => '0',
            disable_chainout => '0',
            resulta          => RESULT
        );

end architecture;
