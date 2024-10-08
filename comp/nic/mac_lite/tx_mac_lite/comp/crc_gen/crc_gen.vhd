-- crc_gen.vhd: CRC gen
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

architecture FULL of TX_MAC_LITE_CRC_GEN is

    signal crc_data_n : std_logic_vector(REGIONS*32-1 downto 0);

begin

    mfb_crc32_ethernet_i : entity work.MFB_CRC32_ETHERNET
    generic map(
        REGIONS        => REGIONS,
        REGION_SIZE    => REGION_SIZE,
        BLOCK_SIZE     => BLOCK_SIZE,
        ITEM_WIDTH     => ITEM_WIDTH,
        USE_DST_RDY    => False,
        IMPLEMENTATION => "PARALLEL",
        CRC_END_IMPL   => CRC_END_IMPL,
        REG_BITMAP     => std_logic_vector(to_unsigned(254,32))
    )
    port map(
        -- CLOCK AND RESET
        CLK           => CLK,
        RESET         => RESET,
        -- INPUT MFB
        RX_DATA       => RX_DATA,
        RX_SOF_POS    => RX_SOF_POS,
        RX_EOF_POS    => RX_EOF_POS,
        RX_SOF        => RX_SOF,
        RX_EOF        => RX_EOF,
        RX_SRC_RDY    => RX_SRC_RDY,
        RX_DST_RDY    => open,
        -- OUTPUT
        CRC32_DATA    => crc_data_n,
        CRC32_VLD     => CRC_VLD,
        CRC32_SRC_RDY => CRC_SRC_RDY,
        CRC32_DST_RDY => '1'
    );

    CRC_DATA <= not crc_data_n;

end architecture;
