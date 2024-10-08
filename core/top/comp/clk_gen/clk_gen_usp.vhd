-- clk_gen_usp.vhd: CLK module for Xilinx UltraScale+ FPGAs
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use IEEE.math_real.all;

use work.math_pack.all;
use work.type_pack.all;

library unisim;
use unisim.vcomponents.all;

architecture USP of COMMON_CLK_GEN is
    signal clkfbout : std_logic;
    signal clkout0  : std_logic;
    signal clkout1  : std_logic;
    signal clkout2  : std_logic;
    signal clkout3  : std_logic;
begin

    INIT_DONE_N <= '0';

    -- NOTE: CLKOUT 0-3 are High-Performance Clocks (UG472), the rest is not!
    mmcm_i : MMCME4_BASE
    generic map (
        BANDWIDTH        => "OPTIMIZED",
        DIVCLK_DIVIDE    => PLL_MASTER_DIV,
        CLKFBOUT_MULT_F  => PLL_MULT_F,
        CLKOUT0_DIVIDE_F => PLL_OUT0_DIV_F,
        CLKOUT1_DIVIDE   => PLL_OUT1_DIV,
        CLKOUT2_DIVIDE   => PLL_OUT2_DIV,
        CLKOUT3_DIVIDE   => PLL_OUT3_DIV,
        CLKOUT4_DIVIDE   => 10,
        CLKOUT5_DIVIDE   => 10,
        CLKOUT6_DIVIDE   => 10,
        CLKIN1_PERIOD    => REFCLK_PERIOD
    ) port map (
        CLKFBOUT  => clkfbout,
        CLKFBOUTB => open,
        CLKOUT0   => clkout0,
        CLKOUT0B  => open,
        CLKOUT1   => clkout1,
        CLKOUT1B  => open,
        CLKOUT2   => clkout2,
        CLKOUT2B  => open,
        CLKOUT3   => clkout3,
        CLKOUT3B  => open,
        CLKOUT4   => open,
        CLKOUT5   => open,
        CLKOUT6   => open,
        CLKFBIN   => clkfbout,
        CLKIN1    => REFCLK,
        LOCKED    => LOCKED,
        PWRDWN    => '0',
        RST       => ASYNC_RESET
    );

    clkout0_buf_i : BUFG
    port map (
       O => OUTCLK_0,
       I => clkout0
    );

    clkout1_buf_i : BUFG
    port map (
       O => OUTCLK_1,
       I => clkout1
    );

    clkout2_buf_i : BUFG
    port map (
       O => OUTCLK_2,
       I => clkout2
    );

    clkout3_buf_i : BUFG
    port map (
       O => OUTCLK_3,
       I => clkout3
    );

end architecture;
