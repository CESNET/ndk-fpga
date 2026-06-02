-- ftile_multirate_eth_8x25g1_8x10g1.vhd: Component declaration for F-Tile Multirate IP 8 x 25g1 (lines) core
-- Base profile 25G FEC(91) Secondary profiles 25G NOFEC, 25G FEC(134), 10G NOFEC
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Jakub Záhora <xzahor06@vutbr.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity FTILE_MULTIRATE_ETH_8X25G1_8X10G1 is
    generic (
        -- ===================================================================
        -- Multirate generic param from NMC (eneable for generating DRP)
        -- ===================================================================
        IP_CNT              : natural := 0;
        -- ===================================================================
        -- Select VSR mode for F-Tile. Values:
        --  - 00 means optical mode configuration (LR/SR)
        --  - 01 means CR mode configuration
        --  - 10 is for cards for which 00 doesn't work due to high loss
        -- ===================================================================
        VSR_MODE_SEL        : std_logic_vector(1 downto 0)
    );
    port (
        -- ===================================================================
        -- MGMT Interface
        -- ===================================================================
        -- MI32 Interface
        MI_RESET_PHY             : in  std_logic;
        MI_CLK_PHY               : in  std_logic;
        MI_DWR                   : in  std_logic_vector(31 downto 0);
        MI_ADDR                  : in  std_logic_vector(31 downto 0);
        MI_RD                    : in  std_logic;
        MI_WR                    : in  std_logic;
        MI_BE                    : in  std_logic_vector( 3 downto 0);
        MI_DRD                   : out std_logic_vector(31 downto 0);
        MI_ARDY                  : out std_logic;
        MI_DRDY                  : out std_logic;
        -- ===================================================================
        -- ETH DATA interface
        -- ===================================================================
        QSFP_TX_P                : out std_logic_vector(1-1 downto 0);
        QSFP_RX_P                : in  std_logic_vector(1-1 downto 0);
        QSFP_TX_N                : out std_logic_vector(1-1 downto 0);
        QSFP_RX_N                : in  std_logic_vector(1-1 downto 0);
        -- ===================================================================
        -- RX ADAPTER interface
        -- ===================================================================
        -- INPUT MAC SEGMENTED INTERFACE (Intel F-Tile IP)
        RX_MACSI_MAC_DATA        : out std_logic_vector(64-1 downto 0);
        RX_MACSI_MAC_INFRAME     : out std_logic;
        RX_MACSI_MAC_EOP_EMPTY   : out std_logic_vector(3-1  downto 0);
        RX_MACSI_MAC_FCS_ERROR   : out std_logic;
        RX_MACSI_MAC_ERROR       : out std_logic_vector(2-1 downto 0);
        RX_MACSI_MAC_STATUS      : out std_logic_vector(3-1 downto 0);
        RX_MACSI_MAC_VALID       : out std_logic;
        -- ===================================================================
        -- TX ADAPTER interface
        -- ===================================================================
        -- OUTPUT MAC SEGMENTED INTERFACE (Intel F-Tile IP)
        TX_MACSI_ADAPT_DATA      : in  std_logic_vector(64-1 downto 0);
        TX_MACSI_ADAPT_INFRAME   : in  std_logic;
        TX_MACSI_ADAPT_EOP_EMPTY : in  std_logic_vector(3-1 downto 0);
        TX_MACSI_ADAPT_ERROR     : in  std_logic;
        TX_MACSI_ADAPT_VALID     : in  std_logic;
        TX_MACSI_MAC_READY       : out std_logic;
        -- ===================================================================
        -- Netvork_MOD_CONE_ENT interface
        -- ===================================================================
        -- different for each ftile (vector)
        CLK_ETH_IN               : in  std_logic;
        CLK_ETH_OUT              : out std_logic;
        RESET_ETH                : in  std_logic;
        -- ===================================================================
        -- ADAPTERS link up
        -- ===================================================================
        RX_LINK_UP               : out std_logic;
        TX_LINK_UP               : out std_logic;
        -- ===================================================================
        -- PLL sigs
        -- ===================================================================
        FTILE_PLL_CLK            : in std_logic;
        FTILE_PLL_REFCLK         : in std_logic
    );
end entity;

architecture FULL of FTILE_MULTIRATE_ETH_8X25G1_8X10G1 is

    component ftile_multirate_eth_1x25g_1x10g is
        port (
            I_CLK_TX                         : in  std_logic                     := 'X';
            I_CLK_RX                         : in  std_logic                     := 'X';
            O_CLK_PLL                        : out std_logic;
            O_SYS_PLL_LOCKED                 : out std_logic;
            I_RECONFIG_CLK                   : in  std_logic                     := 'X';
            I_RECONFIG_RESET                 : in  std_logic                     := 'X';
            O_TX_SERIAL                      : out std_logic_vector(0 downto 0);
            I_RX_SERIAL                      : in  std_logic_vector(0 downto 0)  := (others => 'X');
            O_TX_SERIAL_N                    : out std_logic_vector(0 downto 0);
            I_RX_SERIAL_N                    : in  std_logic_vector(0 downto 0)  := (others => 'X');
            I_CLK_REF                        : in  std_logic                     := 'X';
            I_CLK_SYS                        : in  std_logic                     := 'X';
            O_P0_CLK_TX_DIV                  : out std_logic;
            O_P0_CLK_REC_DIV64               : out std_logic;
            O_P0_CLK_REC_DIV                 : out std_logic;
            I_P0_RST_N                       : in  std_logic                     := 'X';
            I_P0_TX_RST_N                    : in  std_logic                     := 'X';
            I_P0_RX_RST_N                    : in  std_logic                     := 'X';
            O_P0_RST_ACK_N                   : out std_logic;
            O_P0_RX_RST_ACK_N                : out std_logic;
            O_P0_TX_RST_ACK_N                : out std_logic;
            O_P0_TX_PLL_LOCKED               : out std_logic;
            O_P0_CDR_LOCK                    : out std_logic;
            O_P0_TX_LANES_STABLE             : out std_logic;
            O_P0_RX_PCS_READY                : out std_logic;
            I_P0_TX_PAUSE                    : in  std_logic                     := 'X';
            O_P0_RX_PAUSE                    : out std_logic;
            O_P0_RX_BLOCK_LOCK               : out std_logic;
            O_P0_RX_AM_LOCK                  : out std_logic;
            O_P0_LOCAL_FAULT_STATUS          : out std_logic;
            O_P0_REMOTE_FAULT_STATUS         : out std_logic;
            I_P0_STATS_SNAPSHOT              : in  std_logic                     := 'X';
            O_P0_RX_HI_BER                   : out std_logic;
            O_P0_RX_PCS_FULLY_ALIGNED        : out std_logic;
            I_P0_RECONFIG_ETH_ADDR           : in  std_logic_vector(13 downto 0) := (others => 'X');
            I_P0_RECONFIG_ETH_BYTEENABLE     : in  std_logic_vector(3 downto 0)  := (others => 'X');
            O_P0_RECONFIG_ETH_READDATA_VALID : out std_logic;
            I_P0_RECONFIG_ETH_READ           : in  std_logic                     := 'X';
            I_P0_RECONFIG_ETH_WRITE          : in  std_logic                     := 'X';
            O_P0_RECONFIG_ETH_READDATA       : out std_logic_vector(31 downto 0);
            I_P0_RECONFIG_ETH_WRITEDATA      : in  std_logic_vector(31 downto 0) := (others => 'X');
            O_P0_RECONFIG_ETH_WAITREQUEST    : out std_logic;
            I_CLK_PLL                        : in  std_logic                     := 'X';
            I_P0_CLK_TX_TOD                  : in  std_logic                     := 'X';
            I_P0_CLK_RX_TOD                  : in  std_logic                     := 'X';
            I_RECONFIG_XCVR0_ADDR            : in  std_logic_vector(17 downto 0) := (others => 'X');
            I_RECONFIG_XCVR0_BYTEENABLE      : in  std_logic_vector(3 downto 0)  := (others => 'X');
            O_RECONFIG_XCVR0_READDATA_VALID  : out std_logic;
            I_RECONFIG_XCVR0_READ            : in  std_logic                     := 'X';
            I_RECONFIG_XCVR0_WRITE           : in  std_logic                     := 'X';
            O_RECONFIG_XCVR0_READDATA        : out std_logic_vector(31 downto 0);
            I_RECONFIG_XCVR0_WRITEDATA       : in  std_logic_vector(31 downto 0) := (others => 'X');
            O_RECONFIG_XCVR0_WAITREQUEST     : out std_logic;
            I_TX_MAC_DATA                    : in  std_logic_vector(63 downto 0) := (others => 'X');
            I_TX_MAC_VALID                   : in  std_logic                     := 'X';
            I_TX_MAC_INFRAME                 : in  std_logic                     := 'X';
            I_TX_MAC_EOP_EMPTY               : in  std_logic_vector(2 downto 0)  := (others => 'X');
            O_TX_MAC_READY                   : out std_logic;
            I_TX_MAC_ERROR                   : in  std_logic                     := 'X';
            I_TX_MAC_SKIP_CRC                : in  std_logic                     := 'X';
            O_RX_MAC_DATA                    : out std_logic_vector(63 downto 0);
            O_RX_MAC_VALID                   : out std_logic;
            O_RX_MAC_INFRAME                 : out std_logic;
            O_RX_MAC_EOP_EMPTY               : out std_logic_vector(2 downto 0);
            O_RX_MAC_FCS_ERROR               : out std_logic;
            O_RX_MAC_ERROR                   : out std_logic_vector(1 downto 0);
            O_RX_MAC_STATUS                  : out std_logic_vector(2 downto 0)
        );
    end component;

    -- Dynamic reconfiguration controller for the multirate IP
    component dr_ctrl is
        port (
            I_CSR_CLK                     : in  std_logic                     := 'X';
            I_CPU_CLK                     : in  std_logic                     := 'X';
            I_RST_N                       : in  std_logic                     := 'X';
            O_DR_CURR_PROFILE_ID          : out std_logic_vector(14 downto 0);
            O_DR_NEW_CFG_APPLIED          : out std_logic;
            I_DR_NEW_CFG_APPLIED_ACK      : in  std_logic                     := 'X';
            O_DR_IN_PROGRESS              : out std_logic;
            O_DR_ERROR_STATUS             : out std_logic;
            I_DR_HOST_AVMM_ADDRESS        : in  std_logic_vector(9 downto 0)  := (others => 'X');
            O_DR_HOST_AVMM_READDATA_VALID : out std_logic;
            I_DR_HOST_AVMM_READ           : in  std_logic                     := 'X';
            I_DR_HOST_AVMM_WRITE          : in  std_logic                     := 'X';
            O_DR_HOST_AVMM_READDATA       : out std_logic_vector(31 downto 0);
            I_DR_HOST_AVMM_WRITEDATA      : in  std_logic_vector(31 downto 0) := (others => 'X');
            O_DR_HOST_AVMM_WAITREQUEST    : out std_logic
        );
    end component;

    -- Select the usega of DR_CTRL for channel (0)
    function mi_en_map_stat return natural is
    begin
        case IP_CNT is
            when 0      => return 2051; -- represent IP(0) which include dr_ctrl
            when others => return 3;    -- represent others IPs without dr_ctrl (only one need for all IP cores)
        end case;
    end function;

    function mi_en_map_null return natural is
    begin
        case IP_CNT is
            when 0      => return 1; -- represent IP(0) where reconfig_bus(11) from bridgge_drp is used
            when others => return 0; -- represent IPs other then IP(0) where reconfig_bus(11) from bridgge_drp isn't used
        end case;
    end function;

    -- ===================================================================
    -- Constants
    -- ===================================================================
    -- constants for IP core setup
    constant NUM_LANES     : natural   :=  1;
    constant PMA_LANES     : natural   :=  1;
    constant ETH_PORT_CHAN : natural   :=  1;
    constant SPEED         : natural   := 25;
    constant SPEED_CAP     : std_logic_vector(15 downto 0) :=  X"0800";
    constant DEVICE        : string    :=  "AGILEX";
    constant RSFEC_ABLE    : std_logic := '1';
    constant AN_ABLE       : std_logic := '0';

    -- bridge vector lenght constant
    constant MI_SEL_RANGE : natural := 16;

    ---- Adress and data range constants for eth and xcvr
    constant MI_ADDR_WIDTH_PHY : natural := 32;
    constant MI_DATA_WIDTH_PHY : natural := 32;

    --  monitoring RX link state
    constant RX_LINK_CNT_W : natural := 27;

    -- constant for segments for macseg_loop size
    constant SEGMENTS_LOOP : natural := 1;

    -- constants for mac data for TX/RX
    constant MAC_DATA_WIDTH      : natural := 64;
    constant MAC_EOP_EMPTY_WIDTH : natural :=  3;
    constant MAC_ERROR_RX_WIDTH  : natural :=  2;
    constant MAC_STATUS_WIDTH    : natural :=  3;

    -- signals for mgmt => mi_sel interface
    signal drpdo    : std_logic_vector(MI_DATA_WIDTH_PHY-1 downto 0);
    signal drp_drdy : std_logic;
    signal drpen    : std_logic;
    signal drpwe    : std_logic;
    signal drpaddr  : std_logic_vector(MI_ADDR_WIDTH_PHY-1 downto 0);
    signal drpardy  : std_logic;
    signal drpdi    : std_logic_vector(MI_DATA_WIDTH_PHY-1 downto 0);
    signal drpsel   : std_logic_vector(4-1 downto 0);

    -- signals for mi_sel => IP core interface
    signal reconfig_addr           : slv_array_t     (MI_SEL_RANGE-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
    signal reconfig_readdata_valid : std_logic_vector(MI_SEL_RANGE-1 downto 0);
    signal reconfig_read           : std_logic_vector(MI_SEL_RANGE-1 downto 0);
    signal reconfig_write          : std_logic_vector(MI_SEL_RANGE-1 downto 0);
    signal reconfig_readdata       : slv_array_t     (MI_SEL_RANGE-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal reconfig_writedata      : slv_array_t     (MI_SEL_RANGE-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal reconfig_waitrequest    : std_logic_vector(MI_SEL_RANGE-1 downto 0);

    -- signals for multiplexor
    signal reconfig_write_drp       : std_logic_vector(MI_SEL_RANGE-1 downto 0);
    signal reconfig_read_drp        : std_logic_vector(MI_SEL_RANGE-1 downto 0);
    signal reconfig_addr_drp        : slv_array_t     (MI_SEL_RANGE-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
    signal reconfig_writedata_drp   : slv_array_t     (MI_SEL_RANGE-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal reconfig_waitrequest_drp : std_logic_vector(MI_SEL_RANGE-1 downto 0) := (others => '0');

    -- signal for Ftile interface
    signal ftile_rst_ack_n            : std_logic;
    signal ftile_tx_rst_ack_n         : std_logic;
    signal ftile_rx_rst_ack_n         : std_logic;
    signal ftile_tx_lanes_stable      : std_logic;
    signal ftile_rx_pcs_ready         : std_logic;
    -- signal ftile_pll_refclk           : std_logic;
    signal ftile_rx_block_lock        : std_logic;
    signal ftile_rx_am_lock           : std_logic;
    signal ftile_local_fault          : std_logic; -- not used
    signal ftile_remote_fault         : std_logic;
    signal ftile_rx_hi_ber            : std_logic;
    signal ftile_rx_pcs_fully_aligned : std_logic;

    -- signals for sync repeater
    signal ftile_tx_loop_data      : std_logic_vector(MAC_DATA_WIDTH      -1 downto 0);
    signal ftile_tx_loop_valid     : std_logic;
    signal ftile_tx_loop_inframe   : std_logic;
    signal ftile_tx_loop_eop_empty : std_logic_vector(MAC_EOP_EMPTY_WIDTH -1 downto 0);
    signal ftile_tx_loop_ready     : std_logic;
    signal ftile_tx_loop_error     : std_logic;

    -- multiplexor output conected to mac input of IP core
    signal ftile_tx_mac_data       : std_logic_vector(MAC_DATA_WIDTH      -1 downto 0);
    signal ftile_tx_mac_valid      : std_logic;
    signal ftile_tx_mac_inframe    : std_logic;
    signal ftile_tx_mac_eop_empty  : std_logic_vector(MAC_EOP_EMPTY_WIDTH -1 downto 0);
    signal ftile_tx_mac_error      : std_logic;
    signal ftile_tx_mac_ready      : std_logic;

    -- signals from mac output of IP core to Component Out
    signal ftile_rx_mac_data      : std_logic_vector(MAC_DATA_WIDTH       -1 downto 0);
    signal ftile_rx_mac_valid     : std_logic;
    signal ftile_rx_mac_inframe   : std_logic;
    signal ftile_rx_mac_eop_empty : std_logic_vector(MAC_EOP_EMPTY_WIDTH  -1 downto 0);
    signal ftile_rx_mac_fcs_error : std_logic;
    signal ftile_rx_mac_error     : std_logic_vector(MAC_ERROR_RX_WIDTH   -1 downto 0);
    signal ftile_rx_mac_status    : std_logic_vector(MAC_STATUS_WIDTH     -1 downto 0);

    signal mgmt_pcs_reset   : std_logic; -- not used
    signal mgmt_pma_reset   : std_logic;
    signal mgmt_mac_loop    : std_logic;
    signal mgmt_pcs_control : std_logic_vector(16-1 downto 0);
    signal mgmt_pcs_status  : std_logic_vector(16-1 downto 0);

    -- For QuestaSim
    signal mgmt_pcs_control_dummy : std_logic_vector(15-1 downto 0);

    -- Synchronization of REPEATER_CTRL
    -- signal sync_repeater_ctrl : std_logic_vector(REPEATER_CTRL'range);
    signal sync_repeater_ctrl : std_logic;

    signal init_done      : std_logic_vector(PMA_LANES   -1 downto 0);
    signal init_ready     : std_logic_vector(PMA_LANES   -1 downto 0);

    signal rx_link_cnt    : unsigned(RX_LINK_CNT_W-1 downto 0);

    -- Reset sequence controller signals
    signal rst_seq_rst_n     : std_logic;
    signal rst_seq_tx_rst_n  : std_logic;
    signal rst_seq_rx_rst_n  : std_logic;
    signal rst_seq_ready     : std_logic;
    signal rx_link_rst_req   : std_logic;

    signal ftile_clk_out  : std_logic;

begin
    mgmt_i : entity work.MGMT
    generic map (
        NUM_LANES  => NUM_LANES,
        PMA_LANES  => PMA_LANES,
        SPEED      => SPEED,
        SPEED_CAP  => SPEED_CAP,
        DEVICE     => DEVICE,
        RSFEC_ABLE => RSFEC_ABLE,
        AN_ABLE    => AN_ABLE,
        DRP_DWIDTH => MI_DATA_WIDTH_PHY,
        DRP_AWIDTH => MI_ADDR_WIDTH_PHY
    )
    port map (
        RESET                    => MI_RESET_PHY,
        MI_CLK                   => MI_CLK_PHY,
        MI_DWR                   => MI_DWR,
        MI_ADDR                  => MI_ADDR,
        MI_RD                    => MI_RD,
        MI_WR                    => MI_WR,
        MI_BE                    => MI_BE,
        MI_DRD                   => MI_DRD,
        MI_ARDY                  => MI_ARDY,
        MI_DRDY                  => MI_DRDY,
        -- PCS status
        HI_BER                   => ftile_rx_hi_ber,
        BLK_LOCK                 => (others => ftile_rx_block_lock),
        LINKSTATUS               => ftile_rx_pcs_fully_aligned and not ftile_rx_hi_ber,
        BER_COUNT                => (others => '0'),
        BER_COUNT_CLR            => open,
        BLK_ERR_CNTR             => (others => '0'),
        BLK_ERR_CLR              => open,
        SCR_BYPASS               => open,
        PCS_RESET                => mgmt_pcs_reset,                 -- TODO
        PCS_LPBCK                => open,
        PCS_CONTROL(0)           => mgmt_mac_loop,
        PCS_CONTROL(15 downto 1) => mgmt_pcs_control_dummy,
        PCS_CONTROL_I            => mgmt_pcs_control,
        PCS_STATUS               => mgmt_pcs_status,
        -- PCS Lane align
        ALGN_LOCKED              => ftile_rx_am_lock,
        BIP_ERR_CNTRS            => (others => '0'),
        BIP_ERR_CLR              => open,
        LANE_MAP                 => (others => '0'),
        LANE_ALIGN               => (others => ftile_rx_pcs_fully_aligned),
        -- PMA & PMD status/control
        PMA_LOPWR                => open,
        PMA_LPBCK                => open,
        PMA_REM_LPBCK            => open,
        PMA_RESET                => mgmt_pma_reset,                 -- TODO
        PMA_RETUNE               => open,
        PMA_CONTROL              => open,
        PMA_STATUS               => (others => '0'),
        PMA_PTRN_EN              => open,
        PMA_TX_DIS               => open,
        PMA_RX_OK                => (others => ftile_rx_pcs_ready), -- TODO
        PMD_SIG_DET              => (others => ftile_rx_pcs_ready), -- TODO
        PMA_PRECURSOR            => open,
        PMA_POSTCURSOR           => open,
        PMA_DRIVE                => open,
        -- Dynamic reconfiguration interface
        DRPCLK                   => MI_CLK_PHY,
        DRPDO                    => drpdo,
        DRPRDY                   => drp_drdy,                       -- DRDY is set during JTAG operations, therefore using ia_rd as mask
        DRPEN                    => drpen,
        DRPWE                    => drpwe,
        DRPADDR                  => drpaddr,
        DRPARDY                  => drpardy,
        DRPDI                    => drpdi,
        DRPSEL                   => drpsel
    );

    -- MDIO reg 3.4000 (vendor specific PCS control readout)
    mgmt_pcs_control(15 downto 1) <= (others => '0');
    mgmt_pcs_control(0)           <= sync_repeater_ctrl; -- MAC loopback active
    -- MDIO reg 3.4001 (vendor specific PCS status/abilities)
    mgmt_pcs_status(15 downto 1)  <= (others => '0');
    mgmt_pcs_status(0)            <= '1';        -- MAC loopback ability supported

    drp_bridge_i : entity work.BRIDGE_DRP
    generic map (
        MI_DATA_WIDTH_PHY => MI_DATA_WIDTH_PHY,
        MI_ADDR_WIDTH_PHY => MI_ADDR_WIDTH_PHY,
        MI_SEL_RANGE      => MI_SEL_RANGE,
        MI_EN_MAP         => std_logic_vector(to_unsigned(mi_en_map_stat,MI_SEL_RANGE))
    )
    port map (
        DRPCLK                  => MI_CLK_PHY,
        DRPDO                   => drpdo,
        DRP_DRDY                => drp_drdy,
        DRPEN                   => drpen,
        DRPWE                   => drpwe,
        DRPADDR                 => drpaddr,
        DRPARDY                 => drpardy,
        DRPDI                   => drpdi,
        DRPSEL                  => drpsel,

        RECONFIG_ADDR           => reconfig_addr_drp,
        RECONFIG_READDATA_VALID => reconfig_readdata_valid,
        RECONFIG_READ           => reconfig_read_drp,
        RECONFIG_WRITE          => reconfig_write_drp,
        RECONFIG_READDATA       => reconfig_readdata,
        RECONFIG_WRITEDATA      => reconfig_writedata_drp,
        RECONFIG_WAITREQUEST    => reconfig_waitrequest_drp
    );

    -- selection of unused input signals from bridge_drp which have to be conect to '0'
    -- if IP is IP(0) then range is from            (16:12) & (10:2)
    -- if IP is other than IP(0) then range is from (16:11) & (10:2)
    reconfig_readdata_valid (MI_SEL_RANGE-1 downto 11 + mi_en_map_null) <= (others => '0');
    reconfig_readdata_valid (10             downto PMA_LANES+1)         <= (others => '0');
    reconfig_waitrequest    (MI_SEL_RANGE-1 downto 11 + mi_en_map_null) <= (others => '0');
    reconfig_waitrequest    (10             downto PMA_LANES+1)         <= (others => '0');
    reconfig_readdata       (MI_SEL_RANGE-1 downto 11 + mi_en_map_null) <= (others => (others => '0'));
    reconfig_readdata       (10             downto PMA_LANES+1)         <= (others => (others => '0'));

    -- Monitoring RX link state and generating recovery request for FTILE_ETH_RST_SEQ
    process (CLK_ETH_IN)
    begin
        if rising_edge(CLK_ETH_IN) then
            if (rst_seq_ready = '0') then
                -- Reset sequence in progress, hold timer at zero
                rx_link_cnt <= (others => '0');
            elsif (ftile_rx_pcs_ready = '1') then
                -- Link is up, clear the counter
                rx_link_cnt <= (others => '0');
            else
                -- Link is down, increase the counter
                rx_link_cnt <= rx_link_cnt + 1;
            end if;

            -- Trigger RX link recovery when counter reaches ~100ms
            if (rx_link_cnt(RX_LINK_CNT_W-1) = '1' and rx_link_rst_req = '0') then
                rx_link_rst_req <= '1';
            elsif (rst_seq_ready = '0') then
                -- Clear request when reset sequence controller starts processing
                rx_link_rst_req <= '0';
            end if;

            if (RESET_ETH = '1') then
                rx_link_cnt     <= (others => '0');
                rx_link_rst_req <= '0';
            end if;
        end if;
    end process;

    xcvr_reconfig_inf_res_g: for xcvr in PMA_LANES-1 downto 0 generate

        constant IA_INDEX : natural := 1 + xcvr;

        signal init_busy      : std_logic;
        signal init_addr      : std_logic_vector(17 downto 0);
        signal init_read      : std_logic;
        signal init_write     : std_logic;
        signal init_writedata : std_logic_vector(31 downto 0);

    begin

        -- Generate AVMM signals for XCVR blocks
        reconfig_write  (IA_INDEX)    <=
            init_write                   when init_busy = '1'                                      else
            reconfig_write_drp(IA_INDEX) when drpsel = std_logic_vector(to_unsigned(xcvr+1,4))     else
            '0';
        reconfig_read  (IA_INDEX)     <=
            init_read                    when init_busy = '1'                                     else
            reconfig_read_drp (IA_INDEX) when drpsel = std_logic_vector(to_unsigned(xcvr+1,4))    else
            '0';
        reconfig_addr(IA_INDEX)       <=
             X"000" & "00" & init_addr   when init_busy = '1'  else
             reconfig_addr_drp(IA_INDEX)(reconfig_addr(0)'range);
        reconfig_writedata (IA_INDEX) <=
            init_writedata                when init_busy = '1'  else
            reconfig_writedata_drp (IA_INDEX);

        init_done_g: if (xcvr = 0) generate
            init_ready(0)    <= ftile_tx_lanes_stable;
        else generate
            init_ready(xcvr) <= init_done(xcvr-1);
        end generate;

        -- Component ftile_xcvr_init perform set_media_mode() operation to bring the link up on optical media types
        xcvr_init: entity work.FTILE_XCVR_INIT
        generic map (
            PHY_LANE => (3 - (xcvr mod 4)) -- XCVR 0 maps to -> PHY lane 3, XCVR1 -> 2, XCVR2 -> 1 and XCVR3 -> 0
        )
        port map (
            RST              => RESET_ETH or mgmt_pma_reset,
            XCVR_RDY         => init_ready(xcvr),
            CLK              => MI_CLK_PHY,
            ROM_SEL          => VSR_MODE_SEL, -- 00 means optical mode configuration, 01 means CR mode configuration, 10 is for cards for which 00 doesn't work
            BUSY             => init_busy,
            DONE             => init_done(xcvr),
            -- AVMM
            ADDRESS          => init_addr,
            READ             => init_read,
            WRITE            => init_write,
            READDATA         => reconfig_readdata(IA_INDEX),
            READDATA_VALID   => reconfig_readdata_valid(IA_INDEX),
            WRITEDATA        => init_writedata,
            WAITREQUEST      => reconfig_waitrequest(IA_INDEX),
            STATE            => open          -- debug purposes only. Can be left open in the future
        );

        reconfig_waitrequest_drp(IA_INDEX) <= not reconfig_waitrequest(IA_INDEX) and not init_busy;

    end generate;

    reconfig_waitrequest_drp(0) <= not reconfig_waitrequest(0);

    CLK_ETH_OUT <= ftile_clk_out;

    -- =========================================================================
    -- F-Tile Ethernet Reset Sequence Controller
    -- =========================================================================
    rst_seq_i : entity work.FTILE_ETH_RST_SEQ
    port map (
        CLK             => CLK_ETH_IN,
        RST             => RESET_ETH,
        -- Status inputs from F-Tile Ethernet IP
        RST_ACK_N       => ftile_rst_ack_n,
        TX_RST_ACK_N    => ftile_tx_rst_ack_n,
        RX_RST_ACK_N    => ftile_rx_rst_ack_n,
        TX_LANES_STABLE => ftile_tx_lanes_stable,
        RX_PCS_READY    => ftile_rx_pcs_ready,
        -- Reset outputs to F-Tile Ethernet IP (active low)
        RST_N           => rst_seq_rst_n,
        TX_RST_N        => rst_seq_tx_rst_n,
        RX_RST_N        => rst_seq_rx_rst_n,
        -- Status
        READY           => rst_seq_ready,
        -- RX link recovery trigger
        RX_LINK_RST     => rx_link_rst_req
    );
    -- =========================================================================
    -- DR_CTRL
    -- =========================================================================
    -- can't have more than 1 IP component in whole design (1 DR_CTRL for all F-Tile Multirate IP cores)
    dr_ctrl_g : if IP_CNT = 0 generate
        dr_ctrl_i : component dr_ctrl
        port map (
            i_csr_clk                     => MI_CLK_PHY,
            i_cpu_clk                     => MI_CLK_PHY,
            i_rst_n                       => not MI_RESET_PHY,
            o_dr_curr_profile_id          => open,
            o_dr_new_cfg_applied          => open,
            i_dr_new_cfg_applied_ack      => '1',
            o_dr_in_progress              => open,
            o_dr_error_status             => open,
            i_dr_host_avmm_address        => reconfig_addr_drp        (11)(10-1 downto 0),
            o_dr_host_avmm_readdata_valid => reconfig_readdata_valid  (11),
            i_dr_host_avmm_read           => reconfig_read_drp        (11),
            i_dr_host_avmm_write          => reconfig_write_drp       (11),
            o_dr_host_avmm_readdata       => reconfig_readdata        (11),
            i_dr_host_avmm_writedata      => reconfig_writedata_drp   (11),
            o_dr_host_avmm_waitrequest    => reconfig_waitrequest_drp (11)
        );
    end generate;

    -- =========================================================================
    -- F-TILE Ethernet
    -- =========================================================================
    -- can't have more than 8 25g lines devided into 8 channels
    ftile_eth_ip_i : component ftile_multirate_eth_1x25g_1x10g
    port map (
        i_clk_tx                         => CLK_ETH_IN,
        i_clk_rx                         => CLK_ETH_IN,
        o_clk_pll                        => ftile_clk_out,
        o_sys_pll_locked                 => open,
        i_reconfig_clk                   => MI_CLK_PHY,
        i_reconfig_reset                 => MI_RESET_PHY,
        o_tx_serial                      => QSFP_TX_P,
        i_rx_serial                      => QSFP_RX_P,
        o_tx_serial_n                    => QSFP_TX_N,
        i_rx_serial_n                    => QSFP_RX_N,
        i_clk_ref                        => FTILE_PLL_REFCLK,
        i_clk_sys                        => FTILE_PLL_CLK,
        -- ========
        -- |Port 0|
        -- ========
        o_p0_clk_tx_div                  => open,
        o_p0_clk_rec_div64               => open,
        o_p0_clk_rec_div                 => open,
        i_p0_rst_n                       => rst_seq_rst_n,
        i_p0_tx_rst_n                    => rst_seq_tx_rst_n,
        i_p0_rx_rst_n                    => rst_seq_rx_rst_n,
        o_p0_rst_ack_n                   => ftile_rst_ack_n,
        o_p0_rx_rst_ack_n                => ftile_rx_rst_ack_n,
        o_p0_tx_rst_ack_n                => ftile_tx_rst_ack_n,
        o_p0_tx_pll_locked               => open,
        o_p0_cdr_lock                    => open,
        o_p0_tx_lanes_stable             => ftile_tx_lanes_stable,
        o_p0_rx_pcs_ready                => ftile_rx_pcs_ready,
        i_p0_tx_pause                    => '0',
        o_p0_rx_pause                    => open,
        o_p0_rx_block_lock               => ftile_rx_block_lock,
        o_p0_rx_am_lock                  => ftile_rx_am_lock,
        o_p0_local_fault_status          => ftile_local_fault,
        o_p0_remote_fault_status         => ftile_remote_fault,
        i_p0_stats_snapshot              => '0',
        o_p0_rx_hi_ber                   => ftile_rx_hi_ber,
        o_p0_rx_pcs_fully_aligned        => ftile_rx_pcs_fully_aligned,
        -- ethernet reconfig port(0) (+ RSFEC + Transciever) reconfig inf 0x0 for each channel
        i_p0_reconfig_eth_addr           => reconfig_addr_drp       (0)(14-1 downto 0),
        i_p0_reconfig_eth_byteenable     => (others => '1'), -- not supported in MI IA yet
        o_p0_reconfig_eth_readdata_valid => reconfig_readdata_valid (0),
        i_p0_reconfig_eth_read           => reconfig_read_drp       (0),
        i_p0_reconfig_eth_write          => reconfig_write_drp      (0),
        o_p0_reconfig_eth_readdata       => reconfig_readdata       (0),
        i_p0_reconfig_eth_writedata      => reconfig_writedata_drp  (0),
        o_p0_reconfig_eth_waitrequest    => reconfig_waitrequest    (0),
        -- PTP Protocol clk setup
        i_clk_pll                        => '0',
        i_p0_clk_tx_tod                  => '0',
        i_p0_clk_rx_tod                  => '0',
        -- XCVR reconfig inf (0x1)
        i_reconfig_xcvr0_addr            => reconfig_addr           (1)(18-1 downto 0),
        i_reconfig_xcvr0_byteenable      => (others => '1'),
        o_reconfig_xcvr0_readdata_valid  => reconfig_readdata_valid (1),
        i_reconfig_xcvr0_read            => reconfig_read           (1),
        i_reconfig_xcvr0_write           => reconfig_write          (1),
        o_reconfig_xcvr0_readdata        => reconfig_readdata       (1),
        i_reconfig_xcvr0_writedata       => reconfig_writedata      (1),
        o_reconfig_xcvr0_waitrequest     => reconfig_waitrequest    (1),
        -- MAC Status sigs
        i_tx_mac_data                    => ftile_tx_mac_data,
        i_tx_mac_valid                   => ftile_tx_mac_valid,
        i_tx_mac_inframe                 => ftile_tx_mac_inframe,
        i_tx_mac_eop_empty               => ftile_tx_mac_eop_empty,
        o_tx_mac_ready                   => ftile_tx_mac_ready,
        i_tx_mac_error                   => ftile_tx_mac_error,
        i_tx_mac_skip_crc                => '0',
        o_rx_mac_data                    => ftile_rx_mac_data,
        o_rx_mac_valid                   => ftile_rx_mac_valid,
        o_rx_mac_inframe                 => ftile_rx_mac_inframe,
        o_rx_mac_eop_empty               => ftile_rx_mac_eop_empty,
        o_rx_mac_fcs_error               => ftile_rx_mac_fcs_error,
        o_rx_mac_error                   => ftile_rx_mac_error,
        o_rx_mac_status                  => ftile_rx_mac_status
    );

    -- TX interface conected to Component Output
    TX_MACSI_MAC_READY     <= ftile_tx_mac_ready;

    -- RX interface conected to Component Output
    RX_MACSI_MAC_DATA      <= ftile_rx_mac_data;
    RX_MACSI_MAC_VALID     <= ftile_rx_mac_valid;
    RX_MACSI_MAC_INFRAME   <= ftile_rx_mac_inframe;
    RX_MACSI_MAC_EOP_EMPTY <= ftile_rx_mac_eop_empty;
    RX_MACSI_MAC_FCS_ERROR <= ftile_rx_mac_fcs_error;
    RX_MACSI_MAC_ERROR     <= ftile_rx_mac_error;
    RX_MACSI_MAC_STATUS    <= ftile_rx_mac_status;

    process (CLK_ETH_IN)
    begin
        if rising_edge(CLK_ETH_IN) then
            if (MI_RESET_PHY = '1') then
                RX_LINK_UP <= '0';
                TX_LINK_UP <= '0';
            else
                RX_LINK_UP <= rst_seq_ready and ftile_rx_pcs_ready and ftile_rx_pcs_fully_aligned and (not ftile_remote_fault);
                TX_LINK_UP <= rst_seq_ready and ftile_tx_lanes_stable;
            end if;
        end if;
    end process;

    -- Synchronization of REPEATER_CTRL
    sync_repeater_ctrl_i : entity work.ASYNC_BUS_HANDSHAKE
    generic map (
        DATA_WIDTH => ETH_PORT_CHAN
    ) port map (
        ACLK        => MI_CLK_PHY,
        ARST        => MI_RESET_PHY,
        ADATAIN(0)  => mgmt_mac_loop,
        ASEND       => '1',
        AREADY      => open,
        BCLK        => CLK_ETH_IN,
        BRST        => '0',
        BDATAOUT(0) => sync_repeater_ctrl,
        BLOAD       => '1',
        BVALID      => open
    );

    mac_loopback_i: entity work.MACSEG_LOOP
    generic map (
        SEGMENTS => SEGMENTS_LOOP
    )
    port map (
        RST                => RESET_ETH,
        CLK                => CLK_ETH_IN,

        IN_MAC_DATA        => ftile_rx_mac_data,
        IN_MAC_INFRAME(0)  => ftile_rx_mac_inframe,
        IN_MAC_EOP_EMPTY   => ftile_rx_mac_eop_empty,
        IN_MAC_VALID       => ftile_rx_mac_valid,

        OUT_MAC_DATA       => ftile_tx_loop_data,
        OUT_MAC_INFRAME(0) => ftile_tx_loop_inframe,
        OUT_MAC_EOP_EMPTY  => ftile_tx_loop_eop_empty,
        OUT_MAC_ERROR(0)   => ftile_tx_loop_error,
        OUT_MAC_VALID      => ftile_tx_loop_valid,
        OUT_MAC_READY      => ftile_tx_mac_ready
    );

    ftile_tx_mux : process (all)
    begin
        if (sync_repeater_ctrl = '1') then
            -- MAC loopback on
            ftile_tx_mac_data      <= ftile_tx_loop_data;
            ftile_tx_mac_inframe   <= ftile_tx_loop_inframe;
            ftile_tx_mac_eop_empty <= ftile_tx_loop_eop_empty;
            ftile_tx_mac_error     <= ftile_tx_loop_error;
            ftile_tx_mac_valid     <= ftile_tx_loop_valid;
        else
            -- MAC loopback off
            ftile_tx_mac_data      <= TX_MACSI_ADAPT_DATA;
            ftile_tx_mac_inframe   <= TX_MACSI_ADAPT_INFRAME;
            ftile_tx_mac_eop_empty <= TX_MACSI_ADAPT_EOP_EMPTY;
            ftile_tx_mac_error     <= TX_MACSI_ADAPT_ERROR;
            ftile_tx_mac_valid     <= TX_MACSI_ADAPT_VALID;
        end if;
    end process;
end architecture;
