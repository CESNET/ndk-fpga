-- sdm_ctrl_empty.vhd:
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture EMPTY of SDM_CTRL is

begin

    MI_ARDY <= MI_RD or MI_WR;
    MI_DRDY <= MI_RD;
    MI_DRD  <= X"DEADDEAD";
    CHIP_ID <= X"DEADDEADDEADDEAD";

end architecture;
