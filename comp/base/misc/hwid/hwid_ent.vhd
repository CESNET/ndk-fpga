-- hwid_ent.vhd : component for acquisition hardware identification
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Martin Spinler <spinler@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

entity HWID is
    generic(
        DEVICE            : string
    );
    port(
        CLK               : in std_logic;
        XILINX_DNA        : out std_logic_vector(95 downto 0);
        XILINX_DNA_VLD    : out std_logic
    );
end entity;
