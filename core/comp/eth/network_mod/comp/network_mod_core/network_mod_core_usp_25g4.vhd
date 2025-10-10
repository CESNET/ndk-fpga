-- network_mod_core_25g4.vhd: Core of the Network module with 25G4 XILINX PCSPMA
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Vlastimil Kosar <kosar@dyna-nic.com>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;

architecture XXV_G4 of NETWORK_MOD_CORE is

    -- =========================================================================
    --                               CONSTANTS
    -- =========================================================================


    -- =========================================================================
    --                                SIGNALS
    -- =========================================================================

    signal eth_reset_rx_i          : std_logic_vector(3 downto 0);
    signal eth_reset_tx_i          : std_logic_vector(3 downto 0);
    signal eth_clk_mii             : std_logic_vector(3 downto 0);
    signal eth_txd                 : std_logic_vector(256-1 downto 0);
    signal eth_txc                 : std_logic_vector(32-1 downto 0);
    signal eth_rxd                 : std_logic_vector(256-1 downto 0);
    signal eth_rxc                 : std_logic_vector(32-1 downto 0);

    signal eth_txd_reg0            : std_logic_vector(256-1 downto 0);
    signal eth_txc_reg0            : std_logic_vector(32-1 downto 0);
    signal eth_rxd_reg0            : std_logic_vector(256-1 downto 0);
    signal eth_rxc_reg0            : std_logic_vector(32-1 downto 0);

    signal eth_txd_reg1            : std_logic_vector(256-1 downto 0);
    signal eth_txc_reg1            : std_logic_vector(32-1 downto 0);
    signal eth_rxd_reg1            : std_logic_vector(256-1 downto 0);
    signal eth_rxc_reg1            : std_logic_vector(32-1 downto 0);

    signal rx_reset                : std_logic_vector(3 downto 0);
    signal tx_reset                : std_logic_vector(3 downto 0);
    signal reset_eth_int           : std_logic_vector(3 downto 0);

    signal rx_int_mfb_data         : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal rx_int_mfb_sof_pos      : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal rx_int_mfb_eof_pos      : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal rx_int_mfb_sof          : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS-1 downto 0);
    signal rx_int_mfb_eof          : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS-1 downto 0);
    signal rx_int_mfb_src_rdy      : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal rx_int_mfb_dst_rdy      : std_logic_vector(ETH_PORT_CHAN-1 downto 0);

    signal tx_int_mfb_data         : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal tx_int_mfb_error        : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS-1 downto 0);
    signal tx_int_mfb_sof_pos      : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal tx_int_mfb_eof_pos      : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal tx_int_mfb_sof          : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS-1 downto 0);
    signal tx_int_mfb_eof          : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(REGIONS-1 downto 0);
    signal tx_int_mfb_src_rdy      : std_logic_vector(ETH_PORT_CHAN-1 downto 0);

    signal tx_local_fault          : std_logic_vector(3 downto 0);
    signal tx_local_fault_sync     : std_logic_vector(3 downto 0);
begin

    assert (ETH_PORT_CHAN = 4)
        report "NETWORK_MOD_CORE: 25G4 Ethernet IP supports only ETH_PORT_CHAN=4!"
        severity failure;
    assert (ETH_PORT_SPEED = 25)
        report "NETWORK_MOD_CORE: 25G4 Ethernet IP supports only ETH_PORT_SPEED=25!"
        severity failure;

    -- =========================================================================
    --  4x10GE version
    -- =========================================================================
    eth_phy_4x25g_i: entity work.USP_PCS_PMA_WRAPPER
    generic map (
        CH0_MAP           => 0,
        CH1_MAP           => 1,
        CH2_MAP           => 2,
        CH3_MAP           => 3,
        ETH_25G           => true,
        GTY_TX_EQ         => GTY_TX_EQ,
        MI_DATA_WIDTH_PHY => MI_DATA_WIDTH_PHY,
        MI_ADDR_WIDTH_PHY => MI_ADDR_WIDTH_PHY
    )
    port map (
        --! \name Clock and reset signals
        RESET           => MI_RESET_PHY,
        SYSCLK          => MI_CLK_PHY, -- Stable clock, 100 MHz
        --! \name Transceiver reference clock
        REFCLK_P        => QSFP_REFCLK_P,
        REFCLK_N        => QSFP_REFCLK_N,
        --! \name Transceivers 0-3 - serial data
        TX_P            => QSFP_TX_P,
        TX_N            => QSFP_TX_N,
        RX_P            => QSFP_RX_P,
        RX_N            => QSFP_RX_N,
        RXPOLARITY      => LANE_RX_POLARITY,
        TXPOLARITY      => LANE_TX_POLARITY,
        --! \name XGMII interfaces
        TXRESET         => tx_reset,
        XGCLK           => eth_clk_mii,
        TX_LOCAL_FAULT  => tx_local_fault,
        TXD             => eth_txd_reg1,
        TXC             => eth_txc_reg1,
        RXRESET         => rx_reset,
        RXD             => eth_rxd,
        RXC             => eth_rxc,
        -- PMD signal detect
        SIGNAL_DETECT   => "1111",
        -- MI32 interface for management
        MI_CLK          => MI_CLK_PHY,
        MI_DWR          => MI_DWR_PHY,
        MI_ADDR         => MI_ADDR_PHY,
        MI_RD           => MI_RD_PHY,
        MI_WR           => MI_WR_PHY,
        MI_BE           => MI_BE_PHY,
        MI_DRD          => MI_DRD_PHY,
        MI_ARDY         => MI_ARDY_PHY,
        MI_DRDY         => MI_DRDY_PHY
    );


    TX_MFB_CLK   <= eth_clk_mii;
    RX_MFB_CLK   <= eth_clk_mii;
    CLK_ETH      <= eth_clk_mii(0);

    -- =========================================================================
    --  ADAPTERS
    -- =========================================================================

    gen_umii_decs: for i in 0 to ETH_PORT_CHAN - 1 generate
        eth_reset_rx_i(i) <= reset_eth_int(i) or rx_reset(i);
        eth_reset_tx_i(i) <= reset_eth_int(i) or tx_reset(i);

        -- XLGMII Pipeline registers to improve timing
        rx_xlgmii_pipeline_regs_p : process (eth_clk_mii(i))
        begin
            if (eth_clk_mii(i)'event and eth_clk_mii(i) = '1') then
                if (eth_reset_rx_i(i) = '1') then
                    eth_rxd_reg0((i+1)*64-1 downto i*64) <= X"0100009C0100009C";
                    eth_rxc_reg0((i+1)*8-1 downto  i*8)  <= "00010001";

                    eth_rxd_reg1((i+1)*64-1 downto i*64) <= X"0100009C0100009C";
                    eth_rxc_reg1((i+1)*8-1 downto  i*8)  <= "00010001";
                else
                    eth_rxd_reg0((i+1)*64-1 downto i*64) <= eth_rxd((i+1)*64-1 downto i*64);
                    eth_rxc_reg0((i+1)*8-1 downto  i*8)  <= eth_rxc((i+1)*8-1 downto  i*8);

                    eth_rxd_reg1((i+1)*64-1 downto i*64) <= eth_rxd_reg0((i+1)*64-1 downto i*64);
                    eth_rxc_reg1((i+1)*8-1 downto  i*8)  <= eth_rxc_reg0((i+1)*8-1 downto  i*8);
                end if;
            end if;
        end process;
        tx_xlgmii_pipeline_regs_p : process (eth_clk_mii(i))
        begin
            if (eth_clk_mii(i)'event and eth_clk_mii(i) = '1') then
                if (eth_reset_tx_i(i) = '1') then
                    eth_txd_reg0((i+1)*64-1 downto i*64) <= X"0707070707070707";
                    eth_txc_reg0((i+1)*8-1 downto  i*8)  <= (others => '1');

                    eth_txd_reg1((i+1)*64-1 downto i*64) <= X"0707070707070707";
                    eth_txc_reg1((i+1)*8-1 downto  i*8)  <= (others => '1');
                else
                    eth_txd_reg0((i+1)*64-1 downto i*64) <= eth_txd((i+1)*64-1 downto i*64);
                    eth_txc_reg0((i+1)*8-1 downto  i*8)  <= eth_txc((i+1)*8-1 downto  i*8);

                    eth_txd_reg1((i+1)*64-1 downto i*64) <= eth_txd_reg0((i+1)*64-1 downto i*64);
                    eth_txc_reg1((i+1)*8-1 downto  i*8)  <= eth_txc_reg0((i+1)*8-1 downto  i*8);
                end if;
            end if;
        end process;

        xlgmii2mfb_i: entity work.UMII_DEC
        generic map (
            MII_DW           => 64,
            CNT_ERROR_LENGTH => 5,
            XGMII_ALIGN_EN   => true
        )
        port map (
            CLK            => eth_clk_mii(i),
            RESET          => eth_reset_rx_i(i),
            -- =====================================================================
            -- INPUT MII INTERFACE (XGMII, XLGMII, CGMII, CDMII,...)
            -- =====================================================================
            MII_RXD        => eth_rxd_reg1((i+1)*64 - 1 downto i*64),
            MII_RXC        => eth_rxc_reg1((i+1)*8 - 1 downto i*8),
            MII_VLD        => '1',
            -- =====================================================================
            -- OUTPUT MFB LIKE INTERFACE
            -- =====================================================================
            TX_DATA        => tx_int_mfb_data(i),
            TX_SOF_POS     => tx_int_mfb_sof_pos(i),
            TX_EOF_POS     => tx_int_mfb_eof_pos(i),
            TX_SOF         => tx_int_mfb_sof(i),
            TX_EOF         => tx_int_mfb_eof(i),
            TX_ERR         => tx_int_mfb_error(i),
            TX_SRC_RDY     => tx_int_mfb_src_rdy(i),
            -- =====================================================================
            -- OUTPUT LINK STATE INTERFACE
            -- =====================================================================
            LINK_UP        => RX_LINK_UP(i),
            INCOMING_FRAME => open
        );

        mfb2xlgmii_i: entity work.UMII_ENC
        generic map (
            MII_DW      => 64
        )
        port map (
            -- =====================================================================
            -- CLOCK AND RESET
            -- =====================================================================
            CLK        => eth_clk_mii(i),
            RESET      => eth_reset_tx_i(i),
            -- =====================================================================
            -- INPUT MFB LIKE INTERFACE
            -- =====================================================================
            RX_DATA    => rx_int_mfb_data(i),
            RX_SOF_POS => rx_int_mfb_sof_pos(i),
            RX_EOF_POS => rx_int_mfb_eof_pos(i),
            RX_SOF     => rx_int_mfb_sof(i),
            RX_EOF     => rx_int_mfb_eof(i),
            RX_SRC_RDY => rx_int_mfb_src_rdy(i),
            RX_DST_RDY => rx_int_mfb_dst_rdy(i),
            -- =====================================================================
            -- OUTPUT MII INTERFACE (XGMII, XLGMII, CGMII, CDMII,...)
            -- =====================================================================
            MII_TXD    => eth_txd((i+1)*64 - 1 downto i*64),
            MII_TXC    => eth_txc((i+1)*8 - 1 downto i*8),
            MII_VLD    => open,
            MII_RDY    => '1'
        );
    end generate;

    -- =========================================================================
    --  Async crossings
    -- =========================================================================
    gen_async_cross: for i in 0 to ETH_PORT_CHAN - 1 generate
        -- synchronize TX_LINK_UP
        tx_link_up_sync_i : entity work.ASYNC_OPEN_LOOP
        generic map (
            IN_REG  => false,
            TWO_REG => true
        )
        port map (
            ADATAIN  => tx_local_fault(i),
            BCLK     => eth_clk_mii(i),
            BRST     => '0',
            BDATAOUT => tx_local_fault_sync(i)
        );
        TX_LINK_UP(i) <= not tx_local_fault_sync(i);

        -- Synchronize reset
        eth_reset_sync_i: entity work.ASYNC_RESET
        generic map (
            TWO_REG  => false,
            OUT_REG  => true,
            REPLICAS => 1
        )
        port map (
            --! A clock domain
            CLK        => eth_clk_mii(i),
            ASYNC_RST  => RESET_ETH,
            OUT_RST    => reset_eth_int(i downto i)
        );

    end generate;

    TX_MFB_DATA    <= tx_int_mfb_data;
    TX_MFB_MII_ERR <= tx_int_mfb_error;
    TX_MFB_CRC_ERR <= (others => (others => '0'));
    TX_MFB_SOF     <= tx_int_mfb_sof;
    TX_MFB_EOF     <= tx_int_mfb_eof;
    TX_MFB_SOF_POS <= tx_int_mfb_sof_pos;
    TX_MFB_EOF_POS <= tx_int_mfb_eof_pos;
    TX_MFB_SRC_RDY <= tx_int_mfb_src_rdy;

    rx_int_mfb_data    <= RX_MFB_DATA;
    rx_int_mfb_sof     <= RX_MFB_SOF;
    rx_int_mfb_eof     <= RX_MFB_EOF;
    rx_int_mfb_sof_pos <= RX_MFB_SOF_POS;
    rx_int_mfb_eof_pos <= RX_MFB_EOF_POS;
    rx_int_mfb_src_rdy <= RX_MFB_SRC_RDY;
    rx_int_mfb_dst_rdy <= RX_MFB_DST_RDY;
end architecture;
