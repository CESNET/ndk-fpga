-- network_mod_core_ftile.vhd: core of the Network module with Ethernet F-TILE(s).
-- made as system of submodules, where every time is generated just one type of speed by the choosen build
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--            Jakub Záhora <xzahor06@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;

architecture FULL of NETWORK_MOD_CORE is
    -- =========================================================================
    --                        COMPONENTS - PLL and f-tile
    -- =========================================================================
    -- 400g1
	component ftile_pll is
        port (
            out_systempll_synthlock_0 : out std_logic;        -- out_systempll_synthlock
            out_systempll_clk_0       : out std_logic;        -- clk
            out_refclk_fgt_0          : out std_logic;        -- clk
            in_refclk_fgt_0           : in  std_logic := 'X'  -- in_refclk_fgt_0
        );
    end component ftile_pll;

    -- =========================================================================
    --                               FUNCTIONS
    -- =========================================================================
    -- Select the width of RX and TX MAC DATA signals
    function mac_data_width_f return natural is
    begin
        case ETH_PORT_SPEED is
            when 400 => return 1024;
            when 200 => return 512;
            when 100 => return 256;
            when 50  => return 128;
            when 40  => return 128;
            when 25  => return 64;
            when 10  => return 64;
            when others  => return 0;
        end case;
    end function;

    -- Select the width of RX and TX MAC INFRAME signals
    function mac_inframe_width_f return natural is
    begin
        case ETH_PORT_SPEED is
            when 400 => return 16;
            when 200 => return 8;
            when 100 => return 4;
            when 50  => return 2;
            when 40  => return 2;
            when 25  => return 1;
            when 10  => return 1;
            when others  => return 0;
        end case;
    end function;

    -- Select the width of RX and TX MAC EOP EMPTY signals
    function mac_eop_empty_width_f return natural is
    begin
        case ETH_PORT_SPEED is
            when 400 => return 48;
            when 200 => return 24;
            when 100 => return 12;
            when 50  => return 6;
            when 40  => return 6;
            when 25  => return 3;
            when 10  => return 3;
            when others  => return 0;
        end case;
    end function;

    -- Select the width of TX MAC ERROR signal
    function tx_mac_error_width_f return natural is
    begin
        case ETH_PORT_SPEED is
            when 400 => return 16;
            when 200 => return 8;
            when 100 => return 4;
            when 50  => return 2;
            when 40  => return 2;
            when 25  => return 1;
            when 10  => return 1;
            when others  => return 0;
        end case;
    end function;

    -- Select the width of RX MAC FCS ERROR signal
    function rx_mac_fcs_error_width_f return natural is
    begin
        case ETH_PORT_SPEED is
            when 400 => return 16;
            when 200 => return 8;
            when 100 => return 4;
            when 50  => return 2;
            when 40  => return 2;
            when 25  => return 1;
            when 10  => return 1;
            when others  => return 0;
        end case;
    end function;

    -- Select the width of RX MAC ERROR signal
    function rx_mac_error_width_f return natural is
    begin
        case ETH_PORT_SPEED is
            when 400 => return 32;
            when 200 => return 16;
            when 100 => return 8;
            when 50  => return 4;
            when 40  => return 4;
            when 25  => return 2;
            when 10  => return 2;
            when others  => return 0;
        end case;
    end function;

    -- Select the width of RX MAC STATUS signals
    function rx_mac_status_width_f return natural is
    begin
        case ETH_PORT_SPEED is
            when 400 => return 48;
            when 200 => return 24;
            when 100 => return 12;
            when 50  => return 6;
            when 40  => return 6;
            when 25  => return 3;
            when 10  => return 3;
            when others  => return 100;
        end case;
    end function;

    -- =========================================================================
    --                               CONSTANTS
    -- =========================================================================

    constant LANES_PER_CHANNEL      : natural := LANES/ETH_PORT_CHAN;

    -- MAC SEG common constants
    constant MAC_DATA_WIDTH         : natural := mac_data_width_f;
    constant MAC_INFRAME_WIDTH      : natural := mac_inframe_width_f;
    constant MAC_EOP_EMPTY_WIDTH    : natural := mac_eop_empty_width_f;
    -- MAC SEG TX constants
    constant TX_MAC_ERROR_WIDTH     : natural := tx_mac_error_width_f;
    -- MAC SEG RX constants
    constant RX_MAC_FCS_ERROR_WIDTH : natural := rx_mac_fcs_error_width_f;
    constant RX_MAC_ERROR_WIDTH     : natural := rx_mac_error_width_f;
    constant RX_MAC_STATUS_WIDTH    : natural := rx_mac_status_width_f;

    constant MI_ADDR_BASES_PHY      : natural := ETH_PORT_CHAN;  -- look for need of multirate
    constant MGMT_OFF               : std_logic_vector(MI_ADDR_WIDTH_PHY-1 downto 0) := X"0004_0000";

    function mi_addr_base_init_phy_f return slv_array_t is
        variable mi_addr_base_var : slv_array_t(MI_ADDR_BASES_PHY-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
    begin
        for i in 0 to MI_ADDR_BASES_PHY-1 loop
            mi_addr_base_var(i) := std_logic_vector(resize(i*unsigned(MGMT_OFF), MI_ADDR_WIDTH_PHY));
        end loop;
        return mi_addr_base_var;
    end function;

    -- =========================================================================
    --                                SIGNALS
    -- =========================================================================
    signal split_mi_dwr_phy  : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal split_mi_addr_phy : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
    signal split_mi_rd_phy   : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);
    signal split_mi_wr_phy   : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);
    signal split_mi_be_phy   : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_DATA_WIDTH_PHY/8-1 downto 0);
    signal split_mi_ardy_phy : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);
    signal split_mi_drd_phy  : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal split_mi_drdy_phy : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);

    signal qsfp_rx_p_sig : slv_array_t(ETH_PORT_CHAN-1 downto 0)(LANES_PER_CHANNEL-1 downto 0); -- QSFP XCVR RX Data
    signal qsfp_rx_n_sig : slv_array_t(ETH_PORT_CHAN-1 downto 0)(LANES_PER_CHANNEL-1 downto 0); -- QSFP XCVR RX Data
    signal qsfp_tx_p_sig : slv_array_t(ETH_PORT_CHAN-1 downto 0)(LANES_PER_CHANNEL-1 downto 0); -- QSFP XCVR TX Data
    signal qsfp_tx_n_sig : slv_array_t(ETH_PORT_CHAN-1 downto 0)(LANES_PER_CHANNEL-1 downto 0); -- QSFP XCVR TX Data

    signal ftile_clk_out_vec      : std_logic_vector(ETH_PORT_CHAN-1 downto 0); -- in case of multiple IP cores, only one is chosen
    signal ftile_clk_out          : std_logic; -- drives i_clk_rx and i_clk_tx of one or more other IP cores

    signal ftile_pll_clk          : std_logic;
    signal ftile_pll_refclk       : std_logic;

    signal ftile_tx_adapt_data      : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MAC_DATA_WIDTH        -1 downto 0);
    signal ftile_tx_adapt_valid     : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal ftile_tx_adapt_inframe   : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MAC_INFRAME_WIDTH     -1 downto 0);
    signal ftile_tx_adapt_eop_empty : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MAC_EOP_EMPTY_WIDTH   -1 downto 0);
    signal ftile_tx_adapt_error     : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(TX_MAC_ERROR_WIDTH    -1 downto 0);

    signal ftile_tx_mac_ready     : std_logic_vector(ETH_PORT_CHAN-1 downto 0);

    signal ftile_rx_mac_data      : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MAC_DATA_WIDTH        -1 downto 0);
    signal ftile_rx_mac_valid     : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal ftile_rx_mac_inframe   : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MAC_INFRAME_WIDTH     -1 downto 0);
    signal ftile_rx_mac_eop_empty : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MAC_EOP_EMPTY_WIDTH   -1 downto 0);
    signal ftile_rx_mac_fcs_error : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(RX_MAC_FCS_ERROR_WIDTH-1 downto 0);
    signal ftile_rx_mac_error     : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(RX_MAC_ERROR_WIDTH    -1 downto 0);
    signal ftile_rx_mac_status    : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(RX_MAC_STATUS_WIDTH   -1 downto 0);

    -- Verification probe signals
    signal ver_probe_ftile_rx_mac_data      : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MAC_DATA_WIDTH        -1 downto 0);
    signal ver_probe_ftile_rx_mac_valid     : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal ver_probe_ftile_rx_mac_inframe   : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MAC_INFRAME_WIDTH     -1 downto 0);
    signal ver_probe_ftile_rx_mac_eop_empty : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MAC_EOP_EMPTY_WIDTH   -1 downto 0);
    signal ver_probe_ftile_rx_mac_fcs_error : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(RX_MAC_FCS_ERROR_WIDTH-1 downto 0);
    signal ver_probe_ftile_rx_mac_error     : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(RX_MAC_ERROR_WIDTH    -1 downto 0);
    signal ver_probe_ftile_rx_mac_status    : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(RX_MAC_STATUS_WIDTH   -1 downto 0);

    begin

        mi_splitter_i : entity work.MI_SPLITTER_PLUS_GEN
        generic map(
            ADDR_WIDTH  => MI_ADDR_WIDTH_PHY,
            DATA_WIDTH  => MI_DATA_WIDTH_PHY,
            META_WIDTH  => 0,
            PORTS       => MI_ADDR_BASES_PHY,
            PIPE_OUT    => (others => true),
            PIPE_TYPE   => "REG",
            ADDR_BASES  => MI_ADDR_BASES_PHY,
            ADDR_BASE   => mi_addr_base_init_phy_f,
            DEVICE      => DEVICE
        )
        port map(
            CLK     => MI_CLK_PHY,
            RESET   => MI_RESET_PHY,

            RX_DWR  => MI_DWR_PHY,
            RX_MWR  => (others => '0'),
            RX_ADDR => MI_ADDR_PHY,
            RX_BE   => MI_BE_PHY,
            RX_RD   => MI_RD_PHY,
            RX_WR   => MI_WR_PHY,
            RX_ARDY => MI_ARDY_PHY,
            RX_DRD  => MI_DRD_PHY,
            RX_DRDY => MI_DRDY_PHY,

            TX_DWR  => split_mi_dwr_phy,
            TX_MWR  => open,
            TX_ADDR => split_mi_addr_phy,
            TX_BE   => split_mi_be_phy,
            TX_RD   => split_mi_rd_phy,
            TX_WR   => split_mi_wr_phy,
            TX_ARDY => split_mi_ardy_phy,
            TX_DRD  => split_mi_drd_phy,
            TX_DRDY => split_mi_drdy_phy
        );

        -- =========================================================================
        -- F-TILE PLL
        -- =========================================================================
        -- same pll for all IP cores default set to 830,156 MHz
        ftile_pll_ip_i : component ftile_pll
        port map (
            out_systempll_synthlock_0 => open,
            out_systempll_clk_0       => ftile_pll_clk,
            out_refclk_fgt_0          => ftile_pll_refclk,
            in_refclk_fgt_0           => QSFP_REFCLK_P
        );

        -- devide input data to x lines serial lines 
        qsfp_rx_p_sig <= slv_array_deser(QSFP_RX_P, ETH_PORT_CHAN);
        qsfp_rx_n_sig <= slv_array_deser(QSFP_RX_N, ETH_PORT_CHAN);
        QSFP_TX_P     <= slv_array_ser(qsfp_tx_p_sig);
        QSFP_TX_N     <= slv_array_ser(qsfp_tx_n_sig);

        ftile_clk_out <= ftile_clk_out_vec(0);
        CLK_ETH       <= ftile_clk_out;

        -- generic for 400G 8 line line F-Tile IP core 1 time for one card
        ftile_1x400g8_g : if ((ETH_PORT_SPEED = 400) and (EHIP_TYPE = 0))  generate

        eth_ip_g : for i in ETH_PORT_CHAN-1 downto 0 generate
            FTILE_1x400g8_i: entity work.FTILE_1x400G8 
            port map(
                MI_RESET_PHY             => MI_RESET_PHY        ,
                MI_CLK_PHY               => MI_CLK_PHY          ,
                MI_DWR                   => split_mi_dwr_phy (0),
                MI_ADDR                  => split_mi_addr_phy(0),
                MI_RD                    => split_mi_rd_phy  (0),
                MI_WR                    => split_mi_wr_phy  (0),
                MI_BE                    => split_mi_be_phy  (0),
                MI_DRD                   => split_mi_drd_phy (0),
                MI_ARDY                  => split_mi_ardy_phy(0),
                MI_DRDY                  => split_mi_drdy_phy(0),

                QSFP_TX_P                => qsfp_tx_p_sig(0),
                QSFP_RX_P                => qsfp_rx_p_sig(0),
                QSFP_TX_N                => qsfp_tx_n_sig(0),
                QSFP_RX_N                => qsfp_rx_n_sig(0),

                RX_MACSI_MAC_DATA        => ftile_rx_mac_data     (0),
                RX_MACSI_MAC_INFRAME     => ftile_rx_mac_inframe  (0),
                RX_MACSI_MAC_EOP_EMPTY   => ftile_rx_mac_eop_empty(0),
                RX_MACSI_MAC_FCS_ERROR   => ftile_rx_mac_fcs_error(0),
                RX_MACSI_MAC_ERROR       => ftile_rx_mac_error    (0),
                RX_MACSI_MAC_STATUS      => ftile_rx_mac_status   (0),
                RX_MACSI_MAC_VALID       => ftile_rx_mac_valid    (0),

                TX_MACSI_ADAPT_DATA      => ftile_tx_adapt_data     (0),
                TX_MACSI_ADAPT_INFRAME   => ftile_tx_adapt_inframe  (0),
                TX_MACSI_ADAPT_EOP_EMPTY => ftile_tx_adapt_eop_empty(0),
                TX_MACSI_ADAPT_ERROR     => ftile_tx_adapt_error    (0),
                TX_MACSI_ADAPT_VALID     => ftile_tx_adapt_valid    (0),
                TX_MACSI_MAC_READY       => ftile_tx_mac_ready      (0),

                CLK_ETH_OUT              => ftile_clk_out_vec(0),
                RESET_ETH                => RESET_ETH,

                RX_LINK_UP               => RX_LINK_UP(0),
                TX_LINK_UP               => TX_LINK_UP(0),

                FTILE_PLL_CLK            => ftile_pll_clk,
                FTILE_PLL_REFCLK         => ftile_pll_refclk
            );
        end generate;
    end generate ftile_1x400g8_g;

    -- generic for 200G 4 line F-Tile IP core 2 times for one card
    ftile_2x200g4_g : if ((ETH_PORT_SPEED = 200) and (EHIP_TYPE = 0))  generate

        eth_ip_g : for i in ETH_PORT_CHAN-1 downto 0 generate
            ftile_2x200g4_i: entity work.FTILE_2x200g4 
            port map(
                MI_RESET_PHY             => MI_RESET_PHY        ,
                MI_CLK_PHY               => MI_CLK_PHY          ,
                MI_DWR                   => split_mi_dwr_phy (i),
                MI_ADDR                  => split_mi_addr_phy(i),
                MI_RD                    => split_mi_rd_phy  (i),
                MI_WR                    => split_mi_wr_phy  (i),
                MI_BE                    => split_mi_be_phy  (i),
                MI_DRD                   => split_mi_drd_phy (i),
                MI_ARDY                  => split_mi_ardy_phy(i),
                MI_DRDY                  => split_mi_drdy_phy(i),

                QSFP_TX_P                => qsfp_tx_p_sig(i)(4-1 downto 0),
                QSFP_RX_P                => qsfp_rx_p_sig(i)(4-1 downto 0),
                QSFP_TX_N                => qsfp_tx_n_sig(i)(4-1 downto 0),
                QSFP_RX_N                => qsfp_rx_n_sig(i)(4-1 downto 0),

                RX_MACSI_MAC_DATA        => ftile_rx_mac_data     (i),
                RX_MACSI_MAC_INFRAME     => ftile_rx_mac_inframe  (i)(MAC_INFRAME_WIDTH-1 downto 0),
                RX_MACSI_MAC_EOP_EMPTY   => ftile_rx_mac_eop_empty(i),
                RX_MACSI_MAC_FCS_ERROR   => ftile_rx_mac_fcs_error(i)(RX_MAC_FCS_ERROR_WIDTH-1 downto 0),
                RX_MACSI_MAC_ERROR       => ftile_rx_mac_error    (i),
                RX_MACSI_MAC_STATUS      => ftile_rx_mac_status   (i)(24-1 downto 0)   ,
                RX_MACSI_MAC_VALID       => ftile_rx_mac_valid    (i),

                TX_MACSI_ADAPT_DATA      => ftile_tx_adapt_data     (i),
                TX_MACSI_ADAPT_INFRAME   => ftile_tx_adapt_inframe  (i)(MAC_INFRAME_WIDTH-1 downto 0),
                TX_MACSI_ADAPT_EOP_EMPTY => ftile_tx_adapt_eop_empty(i),
                TX_MACSI_ADAPT_ERROR     => ftile_tx_adapt_error    (i)(TX_MAC_ERROR_WIDTH    -1 downto 0),
                TX_MACSI_ADAPT_VALID     => ftile_tx_adapt_valid    (i),
                TX_MACSI_MAC_READY       => ftile_tx_mac_ready      (i),

                CLK_ETH_OUT              => ftile_clk_out_vec(i),
                RESET_ETH                => RESET_ETH,

                RX_LINK_UP               => RX_LINK_UP(i),
                TX_LINK_UP               => TX_LINK_UP(i),

                FTILE_PLL_CLK            => ftile_pll_clk,
                FTILE_PLL_REFCLK         => ftile_pll_refclk
            );
        end generate;
    end generate ftile_2x200g4_g;

    -- generic for 100G 2 line F-Tile IP core 4 times for one card
    ftile_4x100g2_g : if (((ETH_PORT_SPEED = 100) and (EHIP_TYPE = 0)) and (ETH_PORT_CHAN = 4))  generate

        eth_ip_g : for i in ETH_PORT_CHAN-1 downto 0 generate
            FTILE_4x100g2_i: entity work.FTILE_4x100g2 
            port map(
                MI_RESET_PHY             => MI_RESET_PHY        ,
                MI_CLK_PHY               => MI_CLK_PHY          ,
                MI_DWR                   => split_mi_dwr_phy (i),
                MI_ADDR                  => split_mi_addr_phy(i),
                MI_RD                    => split_mi_rd_phy  (i),
                MI_WR                    => split_mi_wr_phy  (i),
                MI_BE                    => split_mi_be_phy  (i),
                MI_DRD                   => split_mi_drd_phy (i),
                MI_ARDY                  => split_mi_ardy_phy(i),
                MI_DRDY                  => split_mi_drdy_phy(i),

                QSFP_TX_P                => qsfp_tx_p_sig(i)(2-1 downto 0),
                QSFP_RX_P                => qsfp_rx_p_sig(i)(2-1 downto 0),
                QSFP_TX_N                => qsfp_tx_n_sig(i)(2-1 downto 0),
                QSFP_RX_N                => qsfp_rx_n_sig(i)(2-1 downto 0),

                RX_MACSI_MAC_DATA        => ftile_rx_mac_data     (i)   ,
                RX_MACSI_MAC_INFRAME     => ftile_rx_mac_inframe  (i)(MAC_INFRAME_WIDTH-1 downto 0),
                RX_MACSI_MAC_EOP_EMPTY   => ftile_rx_mac_eop_empty(i)   ,
                RX_MACSI_MAC_FCS_ERROR   => ftile_rx_mac_fcs_error(i)(RX_MAC_FCS_ERROR_WIDTH-1 downto 0),
                RX_MACSI_MAC_ERROR       => ftile_rx_mac_error    (i)   ,
                RX_MACSI_MAC_STATUS      => ftile_rx_mac_status   (i)   ,
                RX_MACSI_MAC_VALID       => ftile_rx_mac_valid    (i)   ,

                TX_MACSI_ADAPT_DATA      => ftile_tx_adapt_data     (i),
                TX_MACSI_ADAPT_INFRAME   => ftile_tx_adapt_inframe  (i)(MAC_INFRAME_WIDTH-1 downto 0),
                TX_MACSI_ADAPT_EOP_EMPTY => ftile_tx_adapt_eop_empty(i),
                TX_MACSI_ADAPT_ERROR     => ftile_tx_adapt_error    (i)(TX_MAC_ERROR_WIDTH    -1 downto 0),
                TX_MACSI_ADAPT_VALID     => ftile_tx_adapt_valid    (i),
                TX_MACSI_MAC_READY       => ftile_tx_mac_ready      (i),

                CLK_ETH_OUT              => ftile_clk_out_vec(i),
                RESET_ETH                => RESET_ETH,

                RX_LINK_UP               => RX_LINK_UP(i),
                TX_LINK_UP               => TX_LINK_UP(i),

                FTILE_PLL_CLK            => ftile_pll_clk,
                FTILE_PLL_REFCLK         => ftile_pll_refclk
            );
        end generate;
    end generate ftile_4x100g2_g;

    -- generic for 100G 4 line F-Tile IP core 2 times for one card
    FTILE_MULTIRATE_ETH_2x100G4_g : if ((ETH_PORT_SPEED = 100) and (EHIP_TYPE = 1) and (ETH_PORT_CHAN = 2))  generate

        eth_ip_g : for i in ETH_PORT_CHAN-1 downto 0 generate
        FTILE_MULTIRATE_ETH_2x100G4_i: entity work.FTILE_MULTIRATE_ETH_2x100G4
            generic map(
                IP_CNT => i
            )
            port map(
                MI_RESET_PHY             => MI_RESET_PHY        ,
                MI_CLK_PHY               => MI_CLK_PHY          ,
                MI_DWR                   => split_mi_dwr_phy (i),
                MI_ADDR                  => split_mi_addr_phy(i),
                MI_RD                    => split_mi_rd_phy  (i),
                MI_WR                    => split_mi_wr_phy  (i),
                MI_BE                    => split_mi_be_phy  (i),
                MI_DRD                   => split_mi_drd_phy (i),
                MI_ARDY                  => split_mi_ardy_phy(i),
                MI_DRDY                  => split_mi_drdy_phy(i),

                QSFP_TX_P                => qsfp_tx_p_sig(i)(4-1 downto 0),
                QSFP_RX_P                => qsfp_rx_p_sig(i)(4-1 downto 0),
                QSFP_TX_N                => qsfp_tx_n_sig(i)(4-1 downto 0),
                QSFP_RX_N                => qsfp_rx_n_sig(i)(4-1 downto 0),

                RX_MACSI_MAC_DATA        => ftile_rx_mac_data     (i)   ,
                RX_MACSI_MAC_INFRAME     => ftile_rx_mac_inframe  (i)(MAC_INFRAME_WIDTH-1 downto 0),
                RX_MACSI_MAC_EOP_EMPTY   => ftile_rx_mac_eop_empty(i)   ,
                RX_MACSI_MAC_FCS_ERROR   => ftile_rx_mac_fcs_error(i)(RX_MAC_FCS_ERROR_WIDTH-1 downto 0),
                RX_MACSI_MAC_ERROR       => ftile_rx_mac_error    (i)   ,
                RX_MACSI_MAC_STATUS      => ftile_rx_mac_status   (i)   ,
                RX_MACSI_MAC_VALID       => ftile_rx_mac_valid    (i)   ,

                TX_MACSI_ADAPT_DATA      => ftile_tx_adapt_data     (i),
                TX_MACSI_ADAPT_INFRAME   => ftile_tx_adapt_inframe  (i)(MAC_INFRAME_WIDTH-1 downto 0),
                TX_MACSI_ADAPT_EOP_EMPTY => ftile_tx_adapt_eop_empty(i),
                TX_MACSI_ADAPT_ERROR     => ftile_tx_adapt_error    (i)(TX_MAC_ERROR_WIDTH    -1 downto 0),
                TX_MACSI_ADAPT_VALID     => ftile_tx_adapt_valid    (i),
                TX_MACSI_MAC_READY       => ftile_tx_mac_ready      (i),

                CLK_ETH_OUT              => ftile_clk_out_vec(i),
                RESET_ETH                => RESET_ETH,

                RX_LINK_UP               => RX_LINK_UP(i),
                TX_LINK_UP               => TX_LINK_UP(i),
    
                FTILE_PLL_CLK            => ftile_pll_clk,
                FTILE_PLL_REFCLK         => ftile_pll_refclk
            );
        end generate;
    end generate FTILE_MULTIRATE_ETH_2x100G4_g;

    -- generic for 100G 4 line F-Tile multirate IP core 2 times for one card
    ftile_2x100g4_g : if (((ETH_PORT_SPEED = 100) and (EHIP_TYPE = 0)) and (ETH_PORT_CHAN = 2))  generate
        eth_ip_g : for i in ETH_PORT_CHAN-1 downto 0 generate
            FTILE_2x100g4_i: entity work.FTILE_2x100g4
            port map(
                MI_RESET_PHY             => MI_RESET_PHY        ,
                MI_CLK_PHY               => MI_CLK_PHY          ,
                MI_DWR                   => split_mi_dwr_phy (i),
                MI_ADDR                  => split_mi_addr_phy(i),
                MI_RD                    => split_mi_rd_phy  (i),
                MI_WR                    => split_mi_wr_phy  (i),
                MI_BE                    => split_mi_be_phy  (i),
                MI_DRD                   => split_mi_drd_phy (i),
                MI_ARDY                  => split_mi_ardy_phy(i),
                MI_DRDY                  => split_mi_drdy_phy(i),

                QSFP_TX_P                => qsfp_tx_p_sig(i)(4-1 downto 0),
                QSFP_RX_P                => qsfp_rx_p_sig(i)(4-1 downto 0),
                QSFP_TX_N                => qsfp_tx_n_sig(i)(4-1 downto 0),
                QSFP_RX_N                => qsfp_rx_n_sig(i)(4-1 downto 0),

                RX_MACSI_MAC_DATA        => ftile_rx_mac_data     (i)   ,
                RX_MACSI_MAC_INFRAME     => ftile_rx_mac_inframe  (i)(MAC_INFRAME_WIDTH-1 downto 0),
                RX_MACSI_MAC_EOP_EMPTY   => ftile_rx_mac_eop_empty(i)   ,
                RX_MACSI_MAC_FCS_ERROR   => ftile_rx_mac_fcs_error(i)(RX_MAC_FCS_ERROR_WIDTH-1 downto 0),
                RX_MACSI_MAC_ERROR       => ftile_rx_mac_error    (i)   ,
                RX_MACSI_MAC_STATUS      => ftile_rx_mac_status   (i)   ,
                RX_MACSI_MAC_VALID       => ftile_rx_mac_valid    (i)   ,

                TX_MACSI_ADAPT_DATA      => ftile_tx_adapt_data     (i),
                TX_MACSI_ADAPT_INFRAME   => ftile_tx_adapt_inframe  (i)(MAC_INFRAME_WIDTH-1 downto 0),
                TX_MACSI_ADAPT_EOP_EMPTY => ftile_tx_adapt_eop_empty(i),
                TX_MACSI_ADAPT_ERROR     => ftile_tx_adapt_error    (i)(TX_MAC_ERROR_WIDTH    -1 downto 0),
                TX_MACSI_ADAPT_VALID     => ftile_tx_adapt_valid    (i),
                TX_MACSI_MAC_READY       => ftile_tx_mac_ready      (i),

                CLK_ETH_OUT              => ftile_clk_out_vec(i),
                RESET_ETH                => RESET_ETH,

                RX_LINK_UP               => RX_LINK_UP(i),
                TX_LINK_UP               => TX_LINK_UP(i),

                FTILE_PLL_CLK            => ftile_pll_clk,
                FTILE_PLL_REFCLK         => ftile_pll_refclk
            );
        end generate;
    end generate ftile_2x100g4_g;

    -- generic for 50G 1 line F-Tile IP core 8 times for one card
    ftile_8x50g1_g : if ((ETH_PORT_SPEED = 50) and (EHIP_TYPE = 0))  generate
        eth_ip_g : for i in ETH_PORT_CHAN-1 downto 0 generate
            FTILE_8x50g1_i: entity work.FTILE_8x50g1 
            port map(
                MI_RESET_PHY             => MI_RESET_PHY        ,
                MI_CLK_PHY               => MI_CLK_PHY          ,
                MI_DWR                   => split_mi_dwr_phy (i),
                MI_ADDR                  => split_mi_addr_phy(i),
                MI_RD                    => split_mi_rd_phy  (i),
                MI_WR                    => split_mi_wr_phy  (i),
                MI_BE                    => split_mi_be_phy  (i),
                MI_DRD                   => split_mi_drd_phy (i),
                MI_ARDY                  => split_mi_ardy_phy(i),
                MI_DRDY                  => split_mi_drdy_phy(i),

                QSFP_TX_P                => qsfp_tx_p_sig(i),
                QSFP_RX_P                => qsfp_rx_p_sig(i),
                QSFP_TX_N                => qsfp_tx_n_sig(i),
                QSFP_RX_N                => qsfp_rx_n_sig(i),

                RX_MACSI_MAC_DATA        => ftile_rx_mac_data     (i),
                RX_MACSI_MAC_INFRAME     => ftile_rx_mac_inframe  (i),
                RX_MACSI_MAC_EOP_EMPTY   => ftile_rx_mac_eop_empty(i),
                RX_MACSI_MAC_FCS_ERROR   => ftile_rx_mac_fcs_error(i),
                RX_MACSI_MAC_ERROR       => ftile_rx_mac_error    (i),
                RX_MACSI_MAC_STATUS      => ftile_rx_mac_status   (i),
                RX_MACSI_MAC_VALID       => ftile_rx_mac_valid    (i),

                TX_MACSI_ADAPT_DATA      => ftile_tx_adapt_data     (i),
                TX_MACSI_ADAPT_INFRAME   => ftile_tx_adapt_inframe  (i),
                TX_MACSI_ADAPT_EOP_EMPTY => ftile_tx_adapt_eop_empty(i),
                TX_MACSI_ADAPT_ERROR     => ftile_tx_adapt_error    (i),
                TX_MACSI_ADAPT_VALID     => ftile_tx_adapt_valid    (i),
                TX_MACSI_MAC_READY       => ftile_tx_mac_ready      (i),

                CLK_ETH_OUT              => ftile_clk_out_vec(i),
                RESET_ETH                => RESET_ETH,

                RX_LINK_UP               => RX_LINK_UP(i),
                TX_LINK_UP               => TX_LINK_UP(i),

                FTILE_PLL_CLK            => ftile_pll_clk,
                FTILE_PLL_REFCLK         => ftile_pll_refclk
            );
        end generate;
    end generate ftile_8x50g1_g;

    -- generic for 40G 4 line F-Tile IP core 2 times for one card
    ftile_2x40g4_g : if ((ETH_PORT_SPEED = 40) and (EHIP_TYPE = 0))  generate
        eth_ip_g : for i in ETH_PORT_CHAN-1 downto 0 generate
            FTILE_2x40g4_i: entity work.FTILE_2x40g4 
            port map(
                MI_RESET_PHY             => MI_RESET_PHY        ,
                MI_CLK_PHY               => MI_CLK_PHY          ,
                MI_DWR                   => split_mi_dwr_phy (i),
                MI_ADDR                  => split_mi_addr_phy(i),
                MI_RD                    => split_mi_rd_phy  (i),
                MI_WR                    => split_mi_wr_phy  (i),
                MI_BE                    => split_mi_be_phy  (i),
                MI_DRD                   => split_mi_drd_phy (i),
                MI_ARDY                  => split_mi_ardy_phy(i),
                MI_DRDY                  => split_mi_drdy_phy(i),

                QSFP_TX_P                => qsfp_tx_p_sig(i),
                QSFP_RX_P                => qsfp_rx_p_sig(i),
                QSFP_TX_N                => qsfp_tx_n_sig(i),
                QSFP_RX_N                => qsfp_rx_n_sig(i),

                RX_MACSI_MAC_DATA        => ftile_rx_mac_data     (i),
                RX_MACSI_MAC_INFRAME     => ftile_rx_mac_inframe  (i),
                RX_MACSI_MAC_EOP_EMPTY   => ftile_rx_mac_eop_empty(i),
                RX_MACSI_MAC_FCS_ERROR   => ftile_rx_mac_fcs_error(i),
                RX_MACSI_MAC_ERROR       => ftile_rx_mac_error    (i),
                RX_MACSI_MAC_STATUS      => ftile_rx_mac_status   (i),
                RX_MACSI_MAC_VALID       => ftile_rx_mac_valid    (i),

                TX_MACSI_ADAPT_DATA      => ftile_tx_adapt_data     (i),
                TX_MACSI_ADAPT_INFRAME   => ftile_tx_adapt_inframe  (i),
                TX_MACSI_ADAPT_EOP_EMPTY => ftile_tx_adapt_eop_empty(i),
                TX_MACSI_ADAPT_ERROR     => ftile_tx_adapt_error    (i),
                TX_MACSI_ADAPT_VALID     => ftile_tx_adapt_valid    (i),
                TX_MACSI_MAC_READY       => ftile_tx_mac_ready      (i),

                CLK_ETH_OUT              => ftile_clk_out_vec(i),
                RESET_ETH                => RESET_ETH,

                RX_LINK_UP               => RX_LINK_UP(i),
                TX_LINK_UP               => TX_LINK_UP(i),

                FTILE_PLL_CLK            => ftile_pll_clk,
                FTILE_PLL_REFCLK         => ftile_pll_refclk
            );
        end generate;
    end generate ftile_2x40g4_g;

    -- generic for 25G 1 line F-Tile IP core 8 times for one card
    ftile_8x25g1_g : if ((ETH_PORT_SPEED = 25) and (EHIP_TYPE = 0))  generate

        eth_ip_g : for i in ETH_PORT_CHAN-1 downto 0 generate
            FTILE_8x25g1_i: entity work.FTILE_8x25g1 
            port map(
                MI_RESET_PHY             => MI_RESET_PHY        ,
                MI_CLK_PHY               => MI_CLK_PHY          ,
                MI_DWR                   => split_mi_dwr_phy (i),
                MI_ADDR                  => split_mi_addr_phy(i),
                MI_RD                    => split_mi_rd_phy  (i),
                MI_WR                    => split_mi_wr_phy  (i),
                MI_BE                    => split_mi_be_phy  (i),
                MI_DRD                   => split_mi_drd_phy (i),
                MI_ARDY                  => split_mi_ardy_phy(i),
                MI_DRDY                  => split_mi_drdy_phy(i),

                QSFP_TX_P                => qsfp_tx_p_sig(i),
                QSFP_RX_P                => qsfp_rx_p_sig(i),
                QSFP_TX_N                => qsfp_tx_n_sig(i),
                QSFP_RX_N                => qsfp_rx_n_sig(i),

                RX_MACSI_MAC_DATA        => ftile_rx_mac_data     (i)   ,
                RX_MACSI_MAC_INFRAME     => ftile_rx_mac_inframe  (i)(0),
                RX_MACSI_MAC_EOP_EMPTY   => ftile_rx_mac_eop_empty(i)   ,
                RX_MACSI_MAC_FCS_ERROR   => ftile_rx_mac_fcs_error(i)(0),
                RX_MACSI_MAC_ERROR       => ftile_rx_mac_error    (i)   ,
                RX_MACSI_MAC_STATUS      => ftile_rx_mac_status   (i)   ,
                RX_MACSI_MAC_VALID       => ftile_rx_mac_valid    (i)   ,

                TX_MACSI_ADAPT_DATA      => ftile_tx_adapt_data     (i),
                TX_MACSI_ADAPT_INFRAME   => ftile_tx_adapt_inframe  (i)(0),
                TX_MACSI_ADAPT_EOP_EMPTY => ftile_tx_adapt_eop_empty(i),
                TX_MACSI_ADAPT_ERROR     => ftile_tx_adapt_error    (i)(0),
                TX_MACSI_ADAPT_VALID     => ftile_tx_adapt_valid    (i),
                TX_MACSI_MAC_READY       => ftile_tx_mac_ready      (i),

                CLK_ETH_OUT              => ftile_clk_out_vec(i),
                RESET_ETH                => RESET_ETH,

                RX_LINK_UP               => RX_LINK_UP(i),
                TX_LINK_UP               => TX_LINK_UP(i),

                FTILE_PLL_CLK            => ftile_pll_clk,
                FTILE_PLL_REFCLK         => ftile_pll_refclk
            );
        end generate;
    end generate ftile_8x25g1_g;

    -- generic for 25G 1 line F-Tile Multirate IP core 8 times for one card
    FTILE_MULTIRATE_ETH_8x25G1_8x10G1_g : if ((ETH_PORT_SPEED = 25) and (EHIP_TYPE = 1))  generate

        eth_ip_g : for i in ETH_PORT_CHAN-1 downto 0 generate
        FTILE_MULTIRATE_ETH_8x25G1_8x10G1_i: entity work.FTILE_MULTIRATE_ETH_8x25G1_8x10G1
            generic map(
                IP_CNT => i
            )
            port map(
                MI_RESET_PHY             => MI_RESET_PHY        ,
                MI_CLK_PHY               => MI_CLK_PHY          ,
                MI_DWR                   => split_mi_dwr_phy (i),
                MI_ADDR                  => split_mi_addr_phy(i),
                MI_RD                    => split_mi_rd_phy  (i),
                MI_WR                    => split_mi_wr_phy  (i),
                MI_BE                    => split_mi_be_phy  (i),
                MI_DRD                   => split_mi_drd_phy (i),
                MI_ARDY                  => split_mi_ardy_phy(i),
                MI_DRDY                  => split_mi_drdy_phy(i),

                QSFP_TX_P                => qsfp_tx_p_sig(i),
                QSFP_RX_P                => qsfp_rx_p_sig(i),
                QSFP_TX_N                => qsfp_tx_n_sig(i),
                QSFP_RX_N                => qsfp_rx_n_sig(i),

                RX_MACSI_MAC_DATA        => ftile_rx_mac_data     (i)   ,
                RX_MACSI_MAC_INFRAME     => ftile_rx_mac_inframe  (i)(0),
                RX_MACSI_MAC_EOP_EMPTY   => ftile_rx_mac_eop_empty(i)   ,
                RX_MACSI_MAC_FCS_ERROR   => ftile_rx_mac_fcs_error(i)(0),
                RX_MACSI_MAC_ERROR       => ftile_rx_mac_error    (i)   ,
                RX_MACSI_MAC_STATUS      => ftile_rx_mac_status   (i)   ,
                RX_MACSI_MAC_VALID       => ftile_rx_mac_valid    (i)   ,

                TX_MACSI_ADAPT_DATA      => ftile_tx_adapt_data     (i),
                TX_MACSI_ADAPT_INFRAME   => ftile_tx_adapt_inframe  (i)(0),
                TX_MACSI_ADAPT_EOP_EMPTY => ftile_tx_adapt_eop_empty(i),
                TX_MACSI_ADAPT_ERROR     => ftile_tx_adapt_error    (i)(0),
                TX_MACSI_ADAPT_VALID     => ftile_tx_adapt_valid    (i),
                TX_MACSI_MAC_READY       => ftile_tx_mac_ready      (i),

                CLK_ETH_OUT              => ftile_clk_out_vec(i),
                RESET_ETH                => RESET_ETH,

                RX_LINK_UP               => RX_LINK_UP(i),
                TX_LINK_UP               => TX_LINK_UP(i),

                FTILE_PLL_CLK            => ftile_pll_clk,
                FTILE_PLL_REFCLK         => ftile_pll_refclk
            );
        end generate;
    end generate FTILE_MULTIRATE_ETH_8x25G1_8x10G1_g;

    -- generic for 10G 1 line F-Tile IP core 8 times for one card
    ftile_8x10g1_g : if ((ETH_PORT_SPEED = 10) and (EHIP_TYPE = 0))  generate

        eth_ip_g : for i in ETH_PORT_CHAN-1 downto 0 generate
            FTILE_8x10g1_i: entity work.FTILE_8x10g1 
            port map(
                MI_RESET_PHY             => MI_RESET_PHY        ,
                MI_CLK_PHY               => MI_CLK_PHY          ,
                MI_DWR                   => split_mi_dwr_phy (i),
                MI_ADDR                  => split_mi_addr_phy(i),
                MI_RD                    => split_mi_rd_phy  (i),
                MI_WR                    => split_mi_wr_phy  (i),
                MI_BE                    => split_mi_be_phy  (i),
                MI_DRD                   => split_mi_drd_phy (i),
                MI_ARDY                  => split_mi_ardy_phy(i),
                MI_DRDY                  => split_mi_drdy_phy(i),

                QSFP_TX_P                => qsfp_tx_p_sig(i),
                QSFP_RX_P                => qsfp_rx_p_sig(i),
                QSFP_TX_N                => qsfp_tx_n_sig(i),
                QSFP_RX_N                => qsfp_rx_n_sig(i),

                RX_MACSI_MAC_DATA        => ftile_rx_mac_data     (i)   ,
                RX_MACSI_MAC_INFRAME     => ftile_rx_mac_inframe  (i)(0),
                RX_MACSI_MAC_EOP_EMPTY   => ftile_rx_mac_eop_empty(i)   ,
                RX_MACSI_MAC_FCS_ERROR   => ftile_rx_mac_fcs_error(i)(0),
                RX_MACSI_MAC_ERROR       => ftile_rx_mac_error    (i)   ,
                RX_MACSI_MAC_STATUS      => ftile_rx_mac_status   (i)   ,
                RX_MACSI_MAC_VALID       => ftile_rx_mac_valid    (i)   ,

                TX_MACSI_ADAPT_DATA      => ftile_tx_adapt_data     (i),
                TX_MACSI_ADAPT_INFRAME   => ftile_tx_adapt_inframe  (i)(0),
                TX_MACSI_ADAPT_EOP_EMPTY => ftile_tx_adapt_eop_empty(i),
                TX_MACSI_ADAPT_ERROR     => ftile_tx_adapt_error    (i)(0),
                TX_MACSI_ADAPT_VALID     => ftile_tx_adapt_valid    (i),
                TX_MACSI_MAC_READY       => ftile_tx_mac_ready      (i),

                CLK_ETH_OUT              => ftile_clk_out_vec(i),
                RESET_ETH                => RESET_ETH,

                RX_LINK_UP               => RX_LINK_UP(i),
                TX_LINK_UP               => TX_LINK_UP(i),

                FTILE_PLL_CLK            => ftile_pll_clk,
                FTILE_PLL_REFCLK         => ftile_pll_refclk
            );
        end generate;
    end generate ftile_8x10g1_g;

    verification_probe_i : entity work.NETWORK_MOD_CORE_FTILE_VER_PROBE
    generic map(
        CHANNELS        => ETH_PORT_CHAN,
        DATA_WIDTH      => MAC_DATA_WIDTH,
        INFRAME_WIDTH   => MAC_INFRAME_WIDTH,
        EOP_EMPTY_WIDTH => MAC_EOP_EMPTY_WIDTH,
        FCS_ERROR_WIDTH => RX_MAC_FCS_ERROR_WIDTH,
        ERROR_WIDTH     => RX_MAC_ERROR_WIDTH,
        STATUS_WIDTH    => RX_MAC_STATUS_WIDTH
    )
    port map(
        IN_MAC_DATA      => ftile_rx_mac_data,
        IN_MAC_INFRAME   => ftile_rx_mac_inframe,
        IN_MAC_EOP_EMPTY => ftile_rx_mac_eop_empty,
        IN_MAC_FCS_ERROR => ftile_rx_mac_fcs_error,
        IN_MAC_ERROR     => ftile_rx_mac_error,
        IN_MAC_STATUS    => ftile_rx_mac_status,
        IN_MAC_VALID     => ftile_rx_mac_valid,

        OUT_MAC_DATA      => ver_probe_ftile_rx_mac_data,
        OUT_MAC_INFRAME   => ver_probe_ftile_rx_mac_inframe,
        OUT_MAC_EOP_EMPTY => ver_probe_ftile_rx_mac_eop_empty,
        OUT_MAC_FCS_ERROR => ver_probe_ftile_rx_mac_fcs_error,
        OUT_MAC_ERROR     => ver_probe_ftile_rx_mac_error,
        OUT_MAC_STATUS    => ver_probe_ftile_rx_mac_status,
        OUT_MAC_VALID     => ver_probe_ftile_rx_mac_valid
    );

    adapts_g : for i in ETH_PORT_CHAN-1 downto 0 generate
        -- =========================================================================
        -- ADAPTERS
        -- =========================================================================
        rx_ftile_adapter_i : entity work.RX_MAC_LITE_ADAPTER_MAC_SEG
        generic map(
            REGIONS     => REGIONS,
            REGION_SIZE => REGION_SIZE
        )
        port map(
            CLK              => ftile_clk_out,
            RESET            => RESET_ETH,
            IN_MAC_DATA      => ver_probe_ftile_rx_mac_data(i),
            IN_MAC_INFRAME   => ver_probe_ftile_rx_mac_inframe(i),
            IN_MAC_EOP_EMPTY => ver_probe_ftile_rx_mac_eop_empty(i),
            IN_MAC_FCS_ERROR => ver_probe_ftile_rx_mac_fcs_error(i),
            IN_MAC_ERROR     => ver_probe_ftile_rx_mac_error(i),
            IN_MAC_STATUS    => ver_probe_ftile_rx_mac_status(i),
            IN_MAC_VALID     => ver_probe_ftile_rx_mac_valid(i),
            OUT_MFB_DATA     => TX_MFB_DATA(i),
            OUT_MFB_ERROR    => TX_MFB_ERROR(i),
            OUT_MFB_SOF      => TX_MFB_SOF(i),
            OUT_MFB_EOF      => TX_MFB_EOF(i),
            OUT_MFB_SOF_POS  => TX_MFB_SOF_POS(i),
            OUT_MFB_EOF_POS  => TX_MFB_EOF_POS(i),
            OUT_MFB_SRC_RDY  => TX_MFB_SRC_RDY(i),
            OUT_LINK_UP      => open
        );
        tx_ftile_adapter_i : entity work.TX_MAC_LITE_ADAPTER_MAC_SEG
        generic map(
            REGIONS     => REGIONS,
            REGION_SIZE => REGION_SIZE
        )
        port map(
            CLK               => ftile_clk_out,
            RESET             => RESET_ETH,
            IN_MFB_DATA       => RX_MFB_DATA(i),
            IN_MFB_SOF        => RX_MFB_SOF(i),
            IN_MFB_EOF        => RX_MFB_EOF(i),
            IN_MFB_SOF_POS    => RX_MFB_SOF_POS(i),
            IN_MFB_EOF_POS    => RX_MFB_EOF_POS(i),
            IN_MFB_ERROR      => (others => '0'),
            IN_MFB_SRC_RDY    => RX_MFB_SRC_RDY(i),
            IN_MFB_DST_RDY    => RX_MFB_DST_RDY(i),
            OUT_MAC_DATA      => ftile_tx_adapt_data(i),
            OUT_MAC_INFRAME   => ftile_tx_adapt_inframe(i),
            OUT_MAC_EOP_EMPTY => ftile_tx_adapt_eop_empty(i),
            OUT_MAC_ERROR     => ftile_tx_adapt_error(i),
            OUT_MAC_VALID     => ftile_tx_adapt_valid(i),
            OUT_MAC_READY     => ftile_tx_mac_ready(i)
        );
    end generate;
end architecture;
