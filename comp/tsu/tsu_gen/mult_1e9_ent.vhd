-- mult_1e9_ent.vhd:
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity MULT_1E9 is
port (
   CLK   : in std_logic;
   DIN   : in std_logic_vector(31 downto 0);
   DOUT  : out std_logic_vector(31 downto 0)
);
end entity;
