-- test_pkg.vhd: Test Package
-- Copyright (C) 2019 CESNET
-- Author: Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use IEEE.math_real.all;
use work.type_pack.all;
use work.math_pack.all;
use work.dma_bus_pack.all;
use work.basics_test_pkg.all;

package test_pkg is

    constant C_WCLK_PER  : time := 4.0 ns;
    constant C_WRST_TIME : time := 10 * C_WCLK_PER + 1 ns;
    constant C_RCLK_PER  : time := 5.0 ns;
    constant C_RRST_TIME : time := 10 * C_RCLK_PER + 1 ns;

    constant RAND_SEED  : positive := 1234;

    constant VER_LENGTH : positive := 100000; -- [WCLK ticks]

    -- Verification settings

    -- a chance, that a write will be preformed each tick
    constant WR_CH : integer := 80; -- [%]
    -- a chance, that a read will be preformed each tick
    constant RD_CH : integer := 80; -- [%]
    -- a chance for PIPE_EN each tick
    constant PIPE_EN_CH : integer := 80; -- [%]

    -- unit generics

    constant DATA_WIDTH   : integer := 34;
    constant ITEMS        : integer := 200;
    constant BLOCK_ENABLE : boolean := True;
    constant BLOCK_WIDTH  : natural := 17;
    constant OUTPUT_REG   : boolean := true;
    constant DEVICE       : string  := "SIM"; -- "STRATIX10"

    -- functions

end package;

package body test_pkg is

end package body;
