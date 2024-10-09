-- network_mod_core_40ge.vhd: Core of the Network module with 40GE Cesnet IP
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;

architecture FOURTY_GIG of NETWORK_MOD_CORE is

    -- =========================================================================
    --                               CONSTANTS
    -- =========================================================================


    -- =========================================================================
    --                                SIGNALS
    -- =========================================================================

    signal ethclk_stable           : std_logic;
    signal eth_reset_i             : std_logic;
    signal eth_clk_156m            : std_logic;
    signal eth_txd                 : std_logic_vector(256-1 downto 0);
    signal eth_txc                 : std_logic_vector(32-1 downto 0);
    signal eth_rxd                 : std_logic_vector(256-1 downto 0);
    signal eth_rxc                 : std_logic_vector(32-1 downto 0);

    signal tx_adapt_data           : std_logic_vector(1*4*8*8-1 downto 0);
    signal tx_adapt_sof_pos        : std_logic_vector(2-1 downto 0);
    signal tx_adapt_eof_pos        : std_logic_vector(5-1 downto 0);
    signal tx_adapt_sof            : std_logic_vector(1-1 downto 0);
    signal tx_adapt_eof            : std_logic_vector(1-1 downto 0);
    signal tx_adapt_error          : std_logic_vector(1-1 downto 0);
    signal tx_adapt_src_rdy        : std_logic;

begin

    assert (ETH_PORT_CHAN = 1)
        report "NETWORK_MOD_CORE: 40GE Ethernet IP supports only ETH_PORT_CHAN=1!"
        severity failure;
    assert (ETH_PORT_SPEED = 40)
        report "NETWORK_MOD_CORE: 40GE Ethernet IP supports only ETH_PORT_SPEED=40!"
        severity failure;

    -- =========================================================================
    --  40GE version
    -- =========================================================================

     ETH_PHY_40: entity work.phy_40ge
     generic map (
         DEVICE    => "ULTRASCALE",
         CLK_SLAVE => false
     )
     port map (
        RESET      => MI_RESET_PHY, --RESET_ETH cannot be used, because it is eth_clk synchronous
        DRPCLK     => MI_CLK_PHY,
        CLK_STABLE => ethclk_stable,
        -- XLGMII interface
        XLGMII_CLK => eth_clk_156m,
        XLGMII_TXD => eth_txd(255 downto 0),
        XLGMII_TXC => eth_txc(31 downto 0),
        XLGMII_RXD => eth_rxd(255 downto 0),
        XLGMII_RXC => eth_rxc(31 downto 0),
        -- Transceiver reference clocks
        REFCLK_P   => QSFP_REFCLK_P,
        REFCLK_N   => QSFP_REFCLK_N,
        REFCLK_OUT => open,
        -- Serial ports - receive
        RXN        => QSFP_RX_N(3 downto 0),
        RXP        => QSFP_RX_P(3 downto 0),
        TXN        => QSFP_TX_N(3 downto 0),
        TXP        => QSFP_TX_P(3 downto 0),
        --
        RXPOLARITY => LANE_RX_POLARITY,
        TXPOLARITY => LANE_TX_POLARITY,
        -- Management (MI32)
        MI_RESET     => MI_RESET_PHY,
        MI_CLK       => MI_CLK_PHY,
        MI_DWR       => MI_DWR_PHY,
        MI_ADDR      => MI_ADDR_PHY,
        MI_RD        => MI_RD_PHY,
        MI_WR        => MI_WR_PHY,
        MI_BE        => MI_BE_PHY,
        MI_DRD       => MI_DRD_PHY,
        MI_ARDY      => MI_ARDY_PHY,
        MI_DRDY      => MI_DRDY_PHY
    );

    CLK_ETH       <= eth_clk_156m;
    eth_reset_i   <= (not ethclk_stable) or RESET_ETH;

    -- =========================================================================
    --  ADAPTERS
    -- =========================================================================

    xlgmii2mfb_i: entity work.UMII_DEC
    generic map (
        MII_DW           => 256,
        CNT_ERROR_LENGTH => 5,
        XGMII_ALIGN_EN   => false
    )
    port map (
        CLK            => eth_clk_156m,
        RESET          => eth_reset_i,
        -- =====================================================================
        -- INPUT MII INTERFACE (XGMII, XLGMII, CGMII, CDMII,...)
        -- =====================================================================
        MII_RXD        => eth_rxd,
        MII_RXC        => eth_rxc,
        MII_VLD        => '1',
        -- =====================================================================
        -- OUTPUT MFB LIKE INTERFACE
        -- =====================================================================
        TX_DATA        => tx_adapt_data,
        TX_SOF_POS     => tx_adapt_sof_pos,
        TX_EOF_POS     => tx_adapt_eof_pos,
        TX_SOF         => tx_adapt_sof,
        TX_EOF         => tx_adapt_eof,
        TX_ERR         => tx_adapt_error,
        TX_SRC_RDY     => tx_adapt_src_rdy,
        -- =====================================================================
        -- OUTPUT LINK STATE INTERFACE
        -- =====================================================================
        LINK_UP        => RX_LINK_UP(0),
        INCOMING_FRAME => open
    );

    TX_MFB_DATA       <= slv_array_deser(tx_adapt_data, 1);
    TX_MFB_ERROR      <= slv_array_deser(tx_adapt_error, 1);
    TX_MFB_SOF_POS    <= slv_array_deser(tx_adapt_sof_pos, 1);
    TX_MFB_EOF_POS    <= slv_array_deser(tx_adapt_eof_pos, 1);
    TX_MFB_SOF        <= slv_array_deser(tx_adapt_sof, 1);
    TX_MFB_EOF        <= slv_array_deser(tx_adapt_eof, 1);
    TX_MFB_SRC_RDY(0) <= tx_adapt_src_rdy;

    mfb2xlgmii_i: entity work.UMII_ENC
    generic map (
        MII_DW      => 256
    )
    port map (
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK        => eth_clk_156m,
        RESET      => eth_reset_i,
        -- =====================================================================
        -- INPUT MFB LIKE INTERFACE
        -- =====================================================================
        RX_DATA    => slv_array_ser(RX_MFB_DATA),
        RX_SOF_POS => slv_array_ser(RX_MFB_SOF_POS),
        RX_EOF_POS => slv_array_ser(RX_MFB_EOF_POS),
        RX_SOF     => slv_array_ser(RX_MFB_SOF),
        RX_EOF     => slv_array_ser(RX_MFB_EOF),
        RX_SRC_RDY => RX_MFB_SRC_RDY(0),
        RX_DST_RDY => RX_MFB_DST_RDY(0),
        -- =====================================================================
        -- OUTPUT MII INTERFACE (XGMII, XLGMII, CGMII, CDMII,...)
        -- =====================================================================
        MII_TXD    => eth_txd,
        MII_TXC    => eth_txc,
        MII_VLD    => open,
        MII_RDY    => '1'
   );

end architecture;
