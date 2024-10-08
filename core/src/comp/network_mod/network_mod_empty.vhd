-- network_mod_empty.vhd: Ethernet MAC and PHY + QSFP control wrapper
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--            Vladislav Valek <valekv@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture EMPTY of NETWORK_MOD is

begin

    CLK_ETH <= (others => CLK_USER);
    TSU_CLK <= CLK_USER;

    TSU_RST <= '0';

    ETH_TX_P <= (others => '1');
    ETH_TX_N <= (others => '0');

    QSFP_I2C_SCL_O  <= (others => '0');
    QSFP_I2C_SCL_OE <= (others => '0');
    QSFP_I2C_SDA_O  <= (others => '0');
    QSFP_I2C_SDA_OE <= (others => '0');
    QSFP_I2C_DIR    <= (others => '0');
    QSFP_MODSEL_N   <= (others => '1');
    QSFP_LPMODE     <= (others => '0');
    QSFP_RESET_N    <= (others => '1');

    -- PORT_ENABLED <= (others => '0');
    ACTIVITY_RX <= (others => '0');
    ACTIVITY_TX <= (others => '0');
    RX_LINK_UP  <= (others => '0');
    TX_LINK_UP  <= (others => '0');

    RX_MFB_DST_RDY <= (others => '1');

    TX_MFB_DATA    <= (others => '0');
    TX_MFB_SOF_POS <= (others => '0');
    TX_MFB_EOF_POS <= (others => '0');
    TX_MFB_SOF     <= (others => '0');
    TX_MFB_EOF     <= (others => '0');
    TX_MFB_SRC_RDY <= (others => '0');

    TX_MVB_DATA    <= (others => '0');
    TX_MVB_VLD     <= (others => '0');
    TX_MVB_SRC_RDY <= (others => '0');

    MI_ARDY <= MI_WR or MI_RD;
    MI_DRDY <= MI_RD;
    MI_DRD  <= (others => '0');

    MI_ARDY_PHY <= MI_WR_PHY or MI_RD_PHY;
    MI_DRDY_PHY <= MI_RD_PHY;
    MI_DRD_PHY  <= (others => '0');

    MI_ARDY_PMD <= MI_WR_PMD or MI_RD_PMD;
    MI_DRDY_PMD <= MI_RD_PMD;
    MI_DRD_PMD  <= (others => '0');

end architecture;
