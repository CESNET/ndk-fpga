-- hwid_empty.vhd : component for acquisition hardware identification
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Martin Spinler <spinler@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

architecture arch of HWID is

begin

    XILINX_DNA      <= (others => '0');
    XILINX_DNA_VLD  <= '0';

end architecture;
