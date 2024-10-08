-- jtag_op_ctrl_empty.vhd:
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture EMPTY of JTAG_OP_CTRL is

begin

    MI_ARDY <= MI_RD or MI_WR;
    MI_DRDY <= MI_RD;
    MI_DRD  <= X"DEADDEAD";

end architecture;
