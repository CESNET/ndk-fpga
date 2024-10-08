-- crc_check_empty.vhd: CRC check
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture EMPTY of RX_MAC_LITE_CRC_CHECK is

begin

    CRC_ERR         <= (others => '0');
    CRC_ERR_VLD     <= (others => '0');
    CRC_ERR_SRC_RDY <= '0';

end architecture;
