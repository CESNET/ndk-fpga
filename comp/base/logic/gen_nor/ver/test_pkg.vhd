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

    constant C_CLK_PER  : time := 4.0 ns;

    constant RAND_SEED  : positive := 1234;

    constant VER_LENGTH : positive := 100000; -- [CLK ticks]

    -- Verification settings

    -- a chance, that a write will be all zeroes
    constant ZEROES_CH : integer := 20; -- [%]

    -- unit generics

    constant DATA_WIDTH   : integer := 289;
    constant DEVICE       : string  := "ULTRASCALE"; -- "STRATIX10"

    -- functions

end package;

package body test_pkg is

end package body;
