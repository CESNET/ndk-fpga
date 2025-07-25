-- clk_gen_altera.vhd: CLK module for Altera FPGAs
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use std.textio.all;

use work.math_pack.all;
use work.type_pack.all;

library altera_lnsim;
use altera_lnsim.altera_lnsim_components.all;

architecture ALTERA of COMMON_CLK_GEN is

    component reset_release_ip is
        port (
            NINIT_DONE : out std_logic
        );
    end component;

    -- Clock frequency of the reference clock signal in MHz
    constant REF_CLK_FREQUENCY : real := 1.0/REFCLK_PERIOD * real(10**3);
    -- It is a simulation specific parameter to select the technology dependent IOPLL simulation model.
    -- Allowed values are:
    -- "Stratix 10", "Agilex 5",
    -- "Agilex 7 F-Series", "Agilex 7 (F-Series)",
    -- "Agilex 7 I-Series", "Agilex 7 (I-Series)",
    -- "Agilex 7 M-Series", "Agilex 7 (M-Series)"
    constant PLL_SIM_MODEL     : string := tsel(DEVICE = "STRATIX10", "Stratix 10", "Agilex 7 F-Series");

    -- Convert REAL to STRING and append units ("MHz")
    function ref_clk_freq_str_f (num: real; decimals: natural) return string is
        constant STR_LEN : natural := integer'image(integer(num))'length + 1 + decimals;
        variable ln      : line;
        variable str     : string(1 to STR_LEN);
    begin
        -- Write the frequency to a line
        write(ln, num, RIGHT, 0, decimals); -- shows frequency with <decimals> decimal points
        -- Read the line into a string
        read(ln, str);
        return str & " MHz";
    end function;

    signal ninit_done : std_logic;
    signal pll_reset  : std_logic;

begin

    reset_release_i : component reset_release_ip
    port map (
        ninit_done => ninit_done
    );

    INIT_DONE_N <= ninit_done;

    pll_reset_g: if INIT_DONE_AS_RESET generate
        pll_reset <= ninit_done;
    else generate
        pll_reset <= ASYNC_RESET;
    end generate;

    ipm_iopll_i : component ipm_iopll
    generic map (
        REFERENCE_CLOCK_FREQUENCY => ref_clk_freq_str_f(REF_CLK_FREQUENCY, 1), -- "100.0 MHz",
        N_CNT                     => PLL_MASTER_DIV,
        M_CNT                     => integer(PLL_MULT_F),
        C0_CNT                    => integer(PLL_OUT0_DIV_F),
        C1_CNT                    => PLL_OUT1_DIV,
        C2_CNT                    => PLL_OUT2_DIV,
        C3_CNT                    => PLL_OUT3_DIV,
        C4_CNT                    => 1,
        C5_CNT                    => 1,
        C6_CNT                    => 1,
        OPERATION_MODE            => "direct",
        CLOCK_TO_COMPENSATE       => 1,
        PHASE_SHIFT0              => 0,
        PHASE_SHIFT1              => 0,
        PHASE_SHIFT2              => 0,
        PHASE_SHIFT3              => 0,
        PHASE_SHIFT4              => 0,
        PHASE_SHIFT5              => 0,
        PHASE_SHIFT6              => 0,
        PLL_SIM_MODEL             => PLL_SIM_MODEL
    )
    port map (
        refclk     => REFCLK,    -- input,  width = 1
        reset      => pll_reset, -- input,  width = 1
        outclk0    => OUTCLK_0,  -- output, width = 1, 400 MHz
        outclk1    => OUTCLK_1,  -- output, width = 1, 300 MHz
        outclk2    => OUTCLK_2,  -- output, width = 1, 200 MHz
        outclk3    => OUTCLK_3,  -- output, width = 1, 100 MHz
        outclk4    => open,      -- output, width = 1
        outclk5    => open,      -- output, width = 1
        outclk6    => open,      -- output, width = 1
        locked     => LOCKED,    -- output, width = 1
        fbclk      => '0',       -- input,  width = 1
        fbclkout   => open,      -- output, width = 1
        extclk_out => open       -- output, width = 1
    -- zdbfbclk   => 'Z'        -- inout,  width = 1
    );

end architecture;
