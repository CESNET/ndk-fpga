-- bmc_wrap_empty.vhd : Wrapper of Bittware BMC
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture EMPTY of BMC_WRAP is

begin

    BMC_IF_PRESENT_N  <= '1';
    QSFPDD0_INT_N     <= '1';
    QSFPDD0_PRESENT_N <= '1';

end architecture;
