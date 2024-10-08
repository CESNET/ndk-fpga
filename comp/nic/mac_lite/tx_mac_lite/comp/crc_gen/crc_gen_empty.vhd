-- crc_gen_empty.vhd: CRC gen
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture EMPTY of TX_MAC_LITE_CRC_GEN is

begin

    CRC_DATA    <= (others => '0');
    CRC_VLD     <= (others => '0');
    CRC_SRC_RDY <= '0';

end architecture;
