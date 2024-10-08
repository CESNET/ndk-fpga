-- altdpram_wrap_empty.vhd: altdpram wrapper
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture EMPTY of ALTDPRAM_WRAP is

begin

    Q <= (others => '0');

end architecture;
