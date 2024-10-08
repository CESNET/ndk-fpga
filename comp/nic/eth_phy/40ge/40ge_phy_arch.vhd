-- 40ge_phy_arch.vhd : The complete 40GBASE-R (PCS+PMA) PHY for Xilinx Ultrascale+ FPGAs
-- Copyright (C) 2010-2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture structural of phy_40ge is

    signal refclk_i          : std_logic;
    signal pma_txreset_done  : std_logic;
    signal pma_rxreset_done  : std_logic;
    signal pma_rxclk_stable  : std_logic;
    signal pma_txclk_stable  : std_logic;
    signal pcs_tx_reset      : std_logic;
    signal pcs_rx_reset      : std_logic;
    signal pcs_tx_reset_i    : std_logic;
    signal pcs_rx_reset_i    : std_logic;
    signal pma_txclk         : std_logic;
    signal pcs_rx_rst_async  : std_logic;
    signal pcs_tx_rst_async  : std_logic;
    signal pma_tx_reset      : std_logic;
    signal pma_tx_reset_async: std_logic;
    signal pma_rx_reset      : std_logic;
    signal pma_rx_reset_async: std_logic;

    signal txd               : std_logic_vector(66*4-1 downto 0);
    signal txready           : std_logic_vector( 3 downto 0);
    signal pma_rx_ok         : std_logic_vector( 3 downto 0);
    signal pma_rxclk_lock    : std_logic_vector( 3 downto 0);
    signal pma_rxclk         : std_logic;
    signal rxd               : std_logic_vector(66*4-1 downto 0);
    signal rxd_valid         : std_logic_vector(3 downto 0);
    signal rxd_ok            : std_logic;
    signal gt_loopback       : std_logic_vector(2 downto 0);
    signal gt_rxpolarity     : std_logic_vector(RXPOLARITY'range);
    signal gt_txpolarity     : std_logic_vector(TXPOLARITY'range);

    --
    signal algn_locked   : std_logic;
    signal bip_err_cntrs : std_logic_vector(4*16-1 downto 0);
    signal lane_map      : std_logic_vector(4*5-1 downto 0);
    signal lane_align    : std_logic_vector(4-1 downto 0);
    signal bip_err_clr   : std_logic_vector(4-1 downto 0);
    signal pma_lpbck     : std_logic;
    signal pma_rem_lpbck : std_logic;
    signal pma_reset     : std_logic;
    signal force_pma_reset: std_logic;
    signal hi_ber        : std_logic;
    signal blk_lock      : std_logic_vector(4-1 downto 0);
    signal linkstatus    : std_logic;
    signal ber_count     : std_logic_vector(21 downto 0);
    signal clr_ber_cnt   : std_logic;
    signal blk_err_cntr  : std_logic_vector(21 downto 0);
    signal blk_err_clr   : std_logic;
    signal rx_scr_bypass : std_logic;
    signal tx_scr_bypass : std_logic;
    signal scr_bypass_i  : std_logic_vector(1 downto 0);
    signal pcs_reset     : std_logic;

    signal am_cntr_o     : std_logic;
    signal am_found_o    : std_logic_vector(3 downto 0);
    signal bip_err_o     : std_logic_vector(3 downto 0);
    signal fifo_dv_o     : std_logic_vector(3 downto 0);
    signal fifo_rd_o     : std_logic_vector(3 downto 0);
    signal fifo_empty_o  : std_logic_vector(3 downto 0);
    signal txdebug_v     : std_logic_vector(15 downto 0);
    signal fifo_full_o   : std_logic_vector(3 downto 0);
    signal rxd_o         : std_logic_vector(66*4-1 downto 0);
    signal txd_o         : std_logic_vector(66*4-1 downto 0);
    signal rxd_ce        : std_logic;
    signal dec_state     : std_logic_vector(4*3-1 downto 0);

    signal xlgmii_rxd_i  : std_logic_vector(255 downto 0);
    signal xlgmii_rxc_i  : std_logic_vector(256/8-1 downto 0);

begin
    -- =========================================================================
    --           Management
    -- =========================================================================
    MGMT: entity work.mgmt
    generic map (
        NUM_LANES     => 4,
        PMA_LANES     => 4,
        SPEED         => 40,
        GBASE40_ABLE  => '1',
        RSFEC_ABLE    => '0',
        AN_ABLE       => '0',
        DEVICE        => DEVICE
    )
    port map (
        RESET         => MI_RESET,
        MI_CLK        => MI_CLK,
        MI_DWR        => MI_DWR,
        MI_ADDR       => MI_ADDR,
        MI_RD         => MI_RD,
        MI_WR         => MI_WR,
        MI_BE         => MI_BE,
        MI_DRD        => MI_DRD,
        MI_ARDY       => MI_ARDY,
        MI_DRDY       => MI_DRDY,
        PCSCLK        => XLGMII_CLK,
        PMACLK        => pma_rxclk,
        -- PMA & PMD status/control
        PMA_LPBCK     => pma_lpbck,
        PMA_REM_LPBCK => pma_rem_lpbck,
        PMA_RX_OK     => pma_rx_ok,
        PMD_SIG_DET   => SIGNAL_DET,
        PMA_RESET     => pma_reset,
        -- PCS Lane align
        ALGN_LOCKED   => algn_locked,
        LANE_MAP      => lane_map,
        LANE_ALIGN    => lane_align,
        BIP_ERR_CNTRS => bip_err_cntrs,
        BIP_ERR_CLR   => bip_err_clr,
        -- PCS status
        HI_BER        => hi_ber,
        BLK_LOCK      => blk_lock,
        LINKSTATUS    => linkstatus,
        BER_COUNT     => ber_count,
        BER_COUNT_CLR => clr_ber_cnt,
        BLK_ERR_CNTR  => blk_err_cntr,
        BLK_ERR_CLR   => blk_err_clr,
        SCR_BYPASS    => scr_bypass_i,
        PCS_RESET     => pcs_reset,
        PCS_LPBCK     => open
    );

    gt_loopback <= pma_rem_lpbck & pma_lpbck & '0';
    -- Disable polarity swaps when local loopback is active
    gt_rxpolarity <= (others => '0') when gt_loopback(1) = '1' else RXPOLARITY;
    gt_txpolarity <= (others => '0') when gt_loopback(1) = '1' else TXPOLARITY;

    GEN_SCR_BYPASS: if (SIMULATION /= 0) generate
        rx_scr_bypass <= '1';
        tx_scr_bypass <= '1';
    end generate;

    NO_SCR_BYPASS: if (SIMULATION = 0) generate

        reclock_rx_scr_bypass_i: entity work.ASYNC_OPEN_LOOP
        generic map(
            IN_REG  => false,
            TWO_REG => false -- Three FFs
        )
        port map(
            ACLK     => '0',
            ARST     => '0',
            BCLK     => pma_rxclk,
            BRST     => '0',
            ADATAIN  => scr_bypass_i(0),
            BDATAOUT => rx_scr_bypass
        );

        reclock_tx_scr_bypass_i: entity work.ASYNC_OPEN_LOOP
        generic map(
            IN_REG  => false,
            TWO_REG => false -- Three FFs
        )
        port map(
            ACLK     => '0',
            ARST     => '0',
            BCLK     => pma_txclk,
            BRST     => '0',
            ADATAIN  => scr_bypass_i(1),
            BDATAOUT => tx_scr_bypass
        );

    end generate;

    -- =========================================================================
    --           TX PCS
    -- =========================================================================
    TX_PATH: entity work.tx_path_40g
    generic map (
        DEVICE    => DEVICE
    )
    port map (
        RESET_PCS  => pcs_tx_reset,
        CLK        => XLGMII_CLK,
        XLGMII_TXD => XLGMII_TXD,
        XLGMII_TXC => XLGMII_TXC,
        --
        SCR_BYPASS => tx_scr_bypass,
        ENC_BYPASS => '0',
        -- HS interface
        RESET_PMA => pma_tx_reset,
        TXCLK     => pma_txclk,
        TXREADY   => txready,
        TXD0      => txd(66*1-1 downto 66*0),
        TXD1      => txd(66*2-1 downto 66*1),
        TXD2      => txd(66*3-1 downto 66*2),
        TXD3      => txd(66*4-1 downto 66*3),
        --
        DEBUG_V   => txdebug_v,
        TXD_O     => txd_o
    );

    -- =========================================================================
    --           RX PCS
    -- =========================================================================
    RX_PATH: entity work.rx_path_40g
    generic map (
        DEVICE    => DEVICE
    )
    port map (
        RESET_PCS     => pcs_rx_reset,
        CLK           => XLGMII_CLK,
        XLGMII_RXD    => XLGMII_RXD,
        XLGMII_RXC    => XLGMII_RXC,
        -- PMA interface
        RESET_PMA     => pma_rx_reset,
        RX_OK         => rxd_ok,
        RXCLK         => pma_rxclk,
        RXD0          => rxd(66*1-1 downto 66*0),
        RXD1          => rxd(66*2-1 downto 66*1),
        RXD2          => rxd(66*3-1 downto 66*2),
        RXD3          => rxd(66*4-1 downto 66*3),
        RXD_VALID     => rxd_valid,
        -- Status/control ports
        BLK_LOCK      => blk_lock,
        HI_BER        => hi_ber,
        LINKSTATUS    => linkstatus,
        BLK_ERR_CNTR  => blk_err_cntr,
        BLK_ERR_CLR   => blk_err_clr,
        SCR_BYPASS    => rx_scr_bypass,
        BER_COUNT     => ber_count,
        BER_CNT_CLR   => clr_ber_cnt,
        LANE_MAP      => lane_map,
        LANES_ALIGNED => lane_align,
        ALIGN_LOCKED  => algn_locked,
        BIP_ERR_CNTRS => bip_err_cntrs,
        BIP_ERR_CLR   => bip_err_clr,
        -- Debug
        AM_CNTR_O     => am_cntr_o,
        AM_FOUND_O    => am_found_o,
        BIP_ERR_O     => bip_err_o,
        FIFO_DV_O     => fifo_dv_o,
        FIFO_RD_O     => fifo_rd_o,
        FIFO_FULL_O   => fifo_full_o,
        FIFO_EMPTY_O  => fifo_empty_o,
        RXD_O         => rxd_o,
        RXD_CE        => rxd_ce,
        DEC_STATE     => dec_state
    );

    -- =========================================================================
    --           PMA
    -- =========================================================================
    PMA: entity work.pma_xlaui_gty
    generic map
    (
        EXAMPLE_SIM_GTRESET_SPEEDUP => "TRUE",     -- simulation setting for GT SecureIP model
        EXAMPLE_SIMULATION          => SIMULATION, -- Set to 1 for simulation
        STABLE_CLOCK_PERIOD         => 10,          --Period of the stable clock driving this state-machine, unit is [ns]
        CLK_SLAVE                   => CLK_SLAVE
    )
    port map (
        REFCLK_N_IN       => REFCLK_N,
        REFCLK_P_IN       => REFCLK_P,
        REFCLK_IN         => REFCLK_IN,
        REFCLK_OUT        => refclk_i,
        DRPCLK_IN         => DRPCLK,
        RESET_IN          => force_pma_reset,
        TXRESET_DONE_OUT  => pma_txreset_done,
        RXRESET_DONE_OUT  => pma_rxreset_done,
        TXCLK_STABLE      => pma_txclk_stable,
        RXCLK_STABLE      => pma_rxclk_stable,
        RX_OK             => pma_rx_ok,
        --
        TXCLK_OUT         => pma_txclk,
        TXDATA_IN         => txd,     -- TXCLK domain
        TXREADY_OUT       => txready, -- TXCLK domain
        RXCLK_OUT         => pma_rxclk,
        RXDATA_OUT        => rxd,       -- RXCLK domain
        RXVALID_OUT       => rxd_valid, -- RXCLK domain
        RX_DATA_OK        => rxd_ok,
        BLK_LOCK_OUT      => blk_lock,  -- RXCLK domain
        --
        RXDETECT_BYPASS   => scr_bypass_i(0),
        SIGNAL_DET        => SIGNAL_DET,
        POWERDOWN_IN      => '0',
        LOOPBACK_IN       => gt_loopback,
        TXPRBSSEL_IN      => "000",  -- TXCLK domain
        TXPRBSFORCEERR_IN => "0000", -- TXCLK domain
        RXPRBSSEL_IN      => "000",  -- RXCLK domain
        RXPRBSERR_OUT     => open,
        RXPOLARITY        => gt_rxpolarity,
        TXPOLARITY        => gt_txpolarity,

        TXN_OUT           => TXN,
        TXP_OUT           => TXP,
        RXN_IN            => RXN,
        RXP_IN            => RXP
    );


    -- =========================================================================
    --           Clocking, resets
    -- =========================================================================
    force_pma_reset  <= RESET or pma_reset;
    XLGMII_CLK       <= pma_txclk;

    -- PCS reset sync - MAC/XLGMII RX side
    pcs_rx_rst_async <=  RESET or (not pma_txclk_stable) or pcs_reset or (not pma_rxreset_done);
    pcs_rx_rst_sync_i: entity work.ASYNC_RESET
    generic map(
        TWO_REG => false
    )
    port map(
        CLK        => XLGMII_CLK,
        ASYNC_RST  => pcs_rx_rst_async,
        OUT_RST(0) => pcs_rx_reset
    );

    -- PCS reset sync - MAC/XLGMII TX side
    pcs_tx_rst_async <=  RESET or (not pma_txclk_stable) or pcs_reset or (not pma_txreset_done);
    pcs_tx_rst_sync_i: entity work.ASYNC_RESET
    generic map(
        TWO_REG => false
    )
    port map(
        CLK        => XLGMII_CLK,
        ASYNC_RST  => pcs_tx_rst_async,
        OUT_RST(0) => pcs_tx_reset
    );

    -- PCS reset sync - PMA TX side
    pma_tx_reset_async <= (not pma_txclk_stable) or RESET or pma_reset;
    PMA_TXRESET_SYNC: entity work.ASYNC_RESET
    generic map(
        TWO_REG => false -- For two reg = true, for three reg = false
    )
    port map(
        CLK        => pma_txclk,
        ASYNC_RST  => pma_tx_reset_async,
        OUT_RST(0) => pma_tx_reset
    );

    -- PCS reset sync - PMA RX side
    pma_rx_reset_async <= (not pma_rxclk_stable) or RESET or pma_reset;
    PMA_RXRESET_SYNC: entity work.ASYNC_RESET
    generic map(
        TWO_REG => false -- For two reg = true, for three reg = false
    )
    port map(
        CLK        => pma_rxclk,
        ASYNC_RST  => pma_rx_reset_async,
        OUT_RST(0) => pma_rx_reset
    );

    -- =========================================================================
    --           Others
    -- =========================================================================
    CLK_STABLE <= pma_txclk_stable;
    REFCLK_OUT <= refclk_i;

end structural;
