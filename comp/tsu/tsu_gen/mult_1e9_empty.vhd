-- mult_10e9_empty.vhd: Empty architecture to be used in Quartus.
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

architecture EMPTY of MULT_1E9 is

begin

    DOUT <= (others => '0');

end architecture;
