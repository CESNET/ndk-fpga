-- clk_gen_intel.vhd: CLK module for Intel FPGAs
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

architecture INTEL of COMMON_CLK_GEN is

    component iopll_ip is
    port (
        rst      : in  std_logic := 'X';
        refclk   : in  std_logic := 'X';
        locked   : out std_logic;
        outclk_0 : out std_logic;
        outclk_1 : out std_logic;
        outclk_2 : out std_logic;
        outclk_3 : out std_logic
    );
    end component iopll_ip;

    component reset_release_ip is
    port (
        ninit_done : out std_logic
    );
    end component reset_release_ip;

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

    iopll_i : component iopll_ip
    port map (
        rst      => pll_reset,
        refclk   => REFCLK,
        locked   => LOCKED,
        outclk_0 => OUTCLK_0, -- 400 MHz
        outclk_1 => OUTCLK_1, -- 300 MHz
        outclk_2 => OUTCLK_2, -- 200 MHz
        outclk_3 => OUTCLK_3  -- 100 MHz
    );

end architecture;
