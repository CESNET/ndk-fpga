-- app_core_empty_arch.vhd: Empty architecture of the application core
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Vladislav Valek <valekv@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture EMPTY of APPLICATION_CORE is

begin

    MI_CLK     <= CLK_USER;
    DMA_CLK    <= CLK_USER_X2;
    DMA_CLK_X2 <= CLK_USER_X4;
    APP_CLK    <= CLK_USER_X2;

    MI_RESET     <= RESET_USER;
    DMA_RESET    <= RESET_USER_X2;
    DMA_RESET_X2 <= RESET_USER_X4;
    APP_RESET    <= RESET_USER_X2;

    ETH_RX_MVB_DST_RDY <= (others => '1');
    ETH_RX_MFB_DST_RDY <= (others => '1');

    ETH_TX_MFB_DATA    <= (others => '0');
    ETH_TX_MFB_HDR     <= (others => '0');
    ETH_TX_MFB_SOF     <= (others => '0');
    ETH_TX_MFB_EOF     <= (others => '0');
    ETH_TX_MFB_SOF_POS <= (others => '0');
    ETH_TX_MFB_EOF_POS <= (others => '0');
    ETH_TX_MFB_SRC_RDY <= (others => '0');

    DMA_RX_MVB_LEN      <= (others => '0');
    DMA_RX_MVB_HDR_META <= (others => '0');
    DMA_RX_MVB_CHANNEL  <= (others => '0');
    DMA_RX_MVB_DISCARD  <= (others => '0');
    DMA_RX_MVB_VLD      <= (others => '0');
    DMA_RX_MVB_SRC_RDY  <= (others => '0');

    DMA_RX_MFB_DATA    <= (others => '0');
    DMA_RX_MFB_SOF     <= (others => '0');
    DMA_RX_MFB_EOF     <= (others => '0');
    DMA_RX_MFB_SOF_POS <= (others => '0');
    DMA_RX_MFB_EOF_POS <= (others => '0');
    DMA_RX_MFB_SRC_RDY <= (others => '0');

    DMA_TX_MVB_DST_RDY <= (others => '1');
    DMA_TX_MFB_DST_RDY <= (others => '1');

    MEM_AVMM_READ       <= (others => '0');
    MEM_AVMM_WRITE      <= (others => '0');
    MEM_AVMM_ADDRESS    <= (others => (others => '0'));
    MEM_AVMM_BURSTCOUNT <= (others => (others => '0'));
    MEM_AVMM_WRITEDATA  <= (others => (others => '0'));

    MEM_REFR_PERIOD <= (others => (others => '0'));
    MEM_REFR_REQ    <= (others => '0');

    EMIF_RST_REQ        <= (others => '0');
    EMIF_AUTO_PRECHARGE <= (others => '0');

    MI_ARDY <= MI_RD or MI_WR;
    MI_DRD  <= (others => '0');
    MI_DRDY <= MI_RD;

end architecture;
