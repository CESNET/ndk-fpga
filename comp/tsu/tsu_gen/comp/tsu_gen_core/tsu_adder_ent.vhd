-- tsu_adder_ent.vhd:
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity TSU_ADDER is
    port (
        CLK        : in  std_logic;
        RESET      : in  std_logic;
        REG_RTR_WE : in  std_logic;
        REG_RTR    : in  std_logic_vector(95 downto 0);
        INCR_VALUE : in  std_logic_vector(38 downto 0);
        ADD_RESULT : out std_logic_vector(95 downto 0)
    );
end entity;
