-- pma_xlaui_gty.vhd : 40GE PMA for Ultrascale FPGA with GTY transceivers
-- Copyright (C) 2018-2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;

entity pma_xlaui_gty is
generic
(
    CLK_SLAVE                    : boolean := false;
    STABLE_CLOCK_PERIOD          : integer   := 8;    --Period of the stable clock driving this state-machine, unit is [ns]
    EXAMPLE_SIM_GTRESET_SPEEDUP  : string    := "TRUE";    -- simulation setting for GT SecureIP model
    EXAMPLE_SIMULATION           : integer   := 0;         -- Set to 1 for simulation
    CS_EN                        : boolean   := false -- Chipscope enable
);
port
(
    REFCLK_N_IN        : in   std_logic; -- 322,27 MHz
    REFCLK_P_IN        : in   std_logic; -- 322,27 MHz
    REFCLK_IN          : in   std_logic := '0'; -- 156,25 MHz - when CLK_SLAVE = true
    REFCLK_OUT         : out  std_logic; -- 161,135 MHz, stable, derived from REFCLK_IN
    TXCLK_OUT          : out  std_logic; -- 161,xxx MHz
    RXCLK_OUT          : out  std_logic; -- 161,xxx MHz
    TXCLK_STABLE       : out  std_logic; --
    RXCLK_STABLE       : out  std_logic; --
    DRPCLK_IN          : in   std_logic; -- 100 MHz
    RESET_IN           : in   std_logic;  -- Async (DRP_CLK domain)
    RXRESET_DONE_OUT   : out  std_logic;  -- Async (DRP_CLK domain)
    TXRESET_DONE_OUT   : out  std_logic;  -- Async (DRP_CLK domain)
    --
    RXDATA_OUT         : out  std_logic_vector(4*66-1 downto 0); -- TXCLK domain
    RXVALID_OUT        : out  std_logic_vector(3 downto 0);      -- TXCLK domain
    TXDATA_IN          : in   std_logic_vector(4*66-1 downto 0); -- TXCLK domain
    TXREADY_OUT        : out  std_logic_vector(3 downto 0);      -- TXCLK domain
    BLK_LOCK_OUT       : out  std_logic_vector(3 downto 0);      -- RXCLK domain
    RX_OK              : out  std_logic_vector(3 downto 0);      -- RXCLK domain
    RX_DATA_OK         : in   std_logic;                         -- Receive
    --
    RXDETECT_BYPASS    : in   std_logic := '0'; -- Bypass RX data detector for SCRAMBLER_BYPASS mode, async
    SIGNAL_DET         : in   std_logic_vector(3 downto 0);  -- not connected
    POWERDOWN_IN       : in   std_logic;  -- Async
    LOOPBACK_IN        : in   std_logic_vector(2 downto 0); -- Async
    TXPRBSSEL_IN       : in   std_logic_vector(2 downto 0); -- TXCLK domain
    TXPRBSFORCEERR_IN  : in   std_logic_vector(3 downto 0); -- TXCLK domain
    RXPRBSSEL_IN       : in   std_logic_vector(2 downto 0); -- RXCLK domain
    RXPRBSERR_OUT      : out  std_logic_vector(3 downto 0); -- RXCLK domain
    RXPOLARITY         : in  std_logic_vector(3 downto 0) := (others => '0');
    TXPOLARITY         : in  std_logic_vector(3 downto 0) := (others => '0');
    -- Serial data
    TXN_OUT            : out  std_logic_vector(3 downto 0);
    TXP_OUT            : out  std_logic_vector(3 downto 0);
    RXN_IN             : in   std_logic_vector(3 downto 0);
    RXP_IN             : in   std_logic_vector(3 downto 0)
);

end pma_xlaui_gty;


architecture USP_GTY of pma_xlaui_gty is

    -- Xilinx IP Core
    COMPONENT gty_40ge
    PORT (
        gtwiz_userclk_tx_reset_in               : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
        gtwiz_userclk_tx_active_in              : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
        gtwiz_userclk_rx_active_in              : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
        gtwiz_reset_clk_freerun_in              : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
        gtwiz_reset_all_in                      : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
        gtwiz_reset_tx_pll_and_datapath_in      : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
        gtwiz_reset_tx_datapath_in              : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
        gtwiz_reset_rx_pll_and_datapath_in      : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
        gtwiz_reset_rx_datapath_in              : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
        gtwiz_reset_rx_cdr_stable_out           : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
        gtwiz_reset_tx_done_out                 : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
        gtwiz_reset_rx_done_out                 : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
        gtwiz_gtye4_cpll_cal_txoutclk_period_in : IN STD_LOGIC_VECTOR(71 DOWNTO 0);
        gtwiz_gtye4_cpll_cal_cnt_tol_in         : IN STD_LOGIC_VECTOR(71 DOWNTO 0);
        gtwiz_gtye4_cpll_cal_bufg_ce_in         : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        gtwiz_userdata_tx_in                    : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        gtwiz_userdata_rx_out                   : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        gtrefclk00_in                           : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
        qpll0outclk_out                         : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
        qpll0outrefclk_out                      : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
        drpclk_in                               : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        gtyrxn_in                               : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        gtyrxp_in                               : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        loopback_in                             : IN STD_LOGIC_VECTOR(11 DOWNTO 0);
        rxgearboxslip_in                        : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        rxpcsreset_in                           : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        rxpd_in                                 : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
        rxpmareset_in                           : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        rxpolarity_in                           : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        rxusrclk_in                             : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        rxusrclk2_in                            : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        txheader_in                             : IN STD_LOGIC_VECTOR(23 DOWNTO 0);
        txpcsreset_in                           : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        txpd_in                                 : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
        txpmareset_in                           : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        txpolarity_in                           : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        txsequence_in                           : IN STD_LOGIC_VECTOR(27 DOWNTO 0);
        txusrclk_in                             : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        txusrclk2_in                            : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        gtpowergood_out                         : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
        gtytxn_out                              : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
        gtytxp_out                              : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
        rxdatavalid_out                         : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
        rxheader_out                            : OUT STD_LOGIC_VECTOR(23 DOWNTO 0);
        rxheadervalid_out                       : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
        rxoutclk_out                            : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
        rxpmaresetdone_out                      : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
        rxprgdivresetdone_out                   : OUT STD_LOGIC_VECTOR(3 DOWNTO 0); -- Async GBX only
        rxresetdone_out                         : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
        rxstartofseq_out                        : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
        txoutclk_out                            : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
        txpmaresetdone_out                      : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
        txprgdivresetdone_out                   : OUT STD_LOGIC_VECTOR(3 DOWNTO 0); -- Async GBX only
        txresetdone_out                         : OUT STD_LOGIC_VECTOR(3 DOWNTO 0)
    );
END COMPONENT;

    constant DLY : time := 1 ns;


    signal  txdata_i                       : std_logic_vector(4*64-1 downto 0);
    signal  txheader_i                     : std_logic_vector(4*6-1 downto 0);
    signal  rxdata_i                       : std_logic_vector(4*64-1 downto 0);
    signal  rxheader_i                     : std_logic_vector(4*6-1 downto 0);
    signal  rxdatavalid_i                  : std_logic_vector(4*2-1 downto 0);
    signal  rxheadervalid_i                : std_logic_vector(4*2-1 downto 0);
    signal  txsequence_i                   : std_logic_vector(4*7-1 downto 0);
    signal  rxgearboxslip_i                : std_logic_vector(4*1-1 downto 0);
    signal  txresetdone_i                  : std_logic_vector(4*1-1 downto 0);
    signal  rxresetdone_i                  : std_logic_vector(4*1-1 downto 0);
    signal  loopback_i                     : std_logic_vector(4*3-1 downto 0);
    signal  powerdown_i                    : std_logic_vector(4*2-1 downto 0);

    signal  gt0_loopback_i                 : std_logic_vector(2 downto 0);
    signal  gt0_rxdata_i                   : std_logic_vector(63 downto 0);
    signal  gt0_rxoutclk_i                 : std_logic;
    signal  gt0_rxdatavalid_i              : std_logic;
    signal  gt0_rxheader_i                 : std_logic_vector(1 downto 0);
    signal  gt0_rxheadervalid_i            : std_logic;
    signal  gt0_rxgearboxslip_i            : std_logic;
    signal  gt0_txheader_i                 : std_logic_vector(1 downto 0);
    signal  gt0_txdata_i                   : std_logic_vector(63 downto 0);
    signal  gt0_txoutclk_i                 : std_logic;

    signal  gt1_loopback_i                 : std_logic_vector(2 downto 0);
    signal  gt1_rxdata_i                   : std_logic_vector(63 downto 0);
    signal  gt1_rxoutclk_i                 : std_logic;
    signal  gt1_rxdatavalid_i              : std_logic;
    signal  gt1_rxheader_i                 : std_logic_vector(1 downto 0);
    signal  gt1_rxheadervalid_i            : std_logic;
    signal  gt1_rxgearboxslip_i            : std_logic;
    signal  gt1_txheader_i                 : std_logic_vector(1 downto 0);
    signal  gt1_txdata_i                   : std_logic_vector(63 downto 0);
    signal  gt1_txoutclk_i                 : std_logic;

    signal  gt2_loopback_i                 : std_logic_vector(2 downto 0);
    signal  gt2_rxdata_i                   : std_logic_vector(63 downto 0);
    signal  gt2_rxoutclk_i                 : std_logic;
    signal  gt2_rxdatavalid_i              : std_logic;
    signal  gt2_rxheader_i                 : std_logic_vector(1 downto 0);
    signal  gt2_rxheadervalid_i            : std_logic;
    signal  gt2_rxgearboxslip_i            : std_logic;
    signal  gt2_txheader_i                 : std_logic_vector(1 downto 0);
    signal  gt2_txdata_i                   : std_logic_vector(63 downto 0);
    signal  gt2_txoutclk_i                 : std_logic;

    signal  gt3_loopback_i                 : std_logic_vector(2 downto 0);
    signal  gt3_rxdata_i                   : std_logic_vector(63 downto 0);
    signal  gt3_rxoutclk_i                 : std_logic;
    signal  gt3_rxdatavalid_i              : std_logic;
    signal  gt3_rxheader_i                 : std_logic_vector(1 downto 0);
    signal  gt3_rxheadervalid_i            : std_logic;
    signal  gt3_rxgearboxslip_i            : std_logic;
    signal  gt3_txheader_i                 : std_logic_vector(1 downto 0);
    signal  gt3_txdata_i                   : std_logic_vector(63 downto 0);
    signal  gt3_txoutclk_i                 : std_logic;

    ------------------------------- Global Signals -----------------------------
    signal  gt0_tx_system_reset_c          : std_logic;
    signal  gt0_rx_system_reset_c          : std_logic;
    signal  gt1_tx_system_reset_c          : std_logic;
    signal  gt1_rx_system_reset_c          : std_logic;
    signal  gt2_tx_system_reset_c          : std_logic;
    signal  gt2_rx_system_reset_c          : std_logic;
    signal  gt3_tx_system_reset_c          : std_logic;
    signal  gt3_rx_system_reset_c          : std_logic;

    signal  tx_resetdone_i                 : std_logic;

    signal  drpclk_in_i                    : std_logic;

    signal  gt0_rx_reset_i                 :   std_logic;
    signal  gt1_rx_reset_i                 :   std_logic;
    signal  gt2_rx_reset_i                 :   std_logic;
    signal  gt3_rx_reset_i                 :   std_logic;

   ------------------------------- User Clocks ---------------------------------
    attribute keep: string;
    signal  gt0_txusrclk_i                  : std_logic;
    signal  gt0_txusrclk2_i                 : std_logic;
    signal  gt0_rxusrclk_i                  : std_logic;
    signal  gt0_rxusrclk2_i                 : std_logic;
    signal  gt_rxusrclk2                    : std_logic;
    signal  gt_txusrclk2                    : std_logic;
    signal  gt1_txusrclk_i                  : std_logic;
    signal  gt1_txusrclk2_i                 : std_logic;
    signal  gt1_rxusrclk_i                  : std_logic;
    signal  gt1_rxusrclk2_i                 : std_logic;
    signal  gt2_txusrclk_i                  : std_logic;
    signal  gt2_txusrclk2_i                 : std_logic;
    signal  gt2_rxusrclk_i                  : std_logic;
    signal  gt2_rxusrclk2_i                 : std_logic;
    signal  gt3_txusrclk_i                  : std_logic;
    signal  gt3_txusrclk2_i                 : std_logic;
    signal  gt3_rxusrclk_i                  : std_logic;
    signal  gt3_rxusrclk2_i                 : std_logic;

    ----------------------------- Reference Clocks ----------------------------
    signal  gtrefclk                        : std_logic;
    signal  gtrefclk_div                    : std_logic;

    ----------------------- Frame check/gen Module Signals --------------------
    signal  gt0_txdatavalid_i               : std_logic;
    signal  gt0_block_lock_i                : std_logic;

    signal  gt1_txdatavalid_i               : std_logic;
    signal  gt1_block_lock_i                : std_logic;

    signal  gt2_txdatavalid_i               : std_logic;
    signal  gt2_block_lock_i                : std_logic;

    signal  gt3_txdatavalid_i               : std_logic;
    signal  gt3_block_lock_i                : std_logic;

    signal  rx_init_done                    : std_logic;
    signal  rxdata_ff                       : std_logic_vector(4*66-1 downto 0);
    signal  rxvalid_ff                      : std_logic_vector(4-1 downto 0);
    signal  rx_toggle_counter0              : unsigned(3 downto 0) := (others => '0');
    signal  rx_toggle_counter1              : unsigned(3 downto 0) := (others => '0');
    signal  rx_toggle_counter2              : unsigned(3 downto 0) := (others => '0');
    signal  rx_toggle_counter3              : unsigned(3 downto 0) := (others => '0');
    signal  rxdata0_toggle                  : std_logic;
    signal  rxdata1_toggle                  : std_logic;
    signal  rxdata2_toggle                  : std_logic;
    signal  rxdata3_toggle                  : std_logic;
    signal  rxdata_ok_i                     : std_logic;

    signal  bufg_gt_ce                      : std_logic_vector(3 downto 0);
    signal  gtwiz_reset_tx_done             : std_logic;
    signal  gtwiz_reset_rx_done             : std_logic;
    signal  reset_all_init                  : std_logic;
    signal  reset_rx_datapath_init          : std_logic;
    signal  rxpmaresetdone                  : std_logic_vector(3 downto 0);
    signal  txpmaresetdone                  : std_logic_vector(3 downto 0);
    signal  txusrrdy_meta                   : std_logic;
    signal  txusrrdy                        : std_logic;
    signal  rxusrrdy_meta                   : std_logic;
    signal  rxusrrdy                        : std_logic;
    signal  gt_rxpolarity                   : std_logic_vector(RXPOLARITY'range);
    signal  gt_txpolarity                   : std_logic_vector(TXPOLARITY'range);

    function reverse (x : std_logic_vector) return std_logic_vector is
    alias alx  : std_logic_vector (x'length - 1 downto 0) is x;
    variable y : std_logic_vector (alx'range);
    begin
         for i in alx'range loop
             y(i) := alx (alx'left - i);
         end loop;

         return y;
    end;

begin

    bufg_gt_ce <= "1111";

    GEN_CLKBUF: if (not CLK_SLAVE) generate

        -- Reference clock (161.135 MHz) global buffer
        -- Output clock is stable, free-running, not affected by resets
        REFCLK_BUFG_GT : BUFG_GT
        port map (
            O       =>  REFCLK_OUT,
            CE      => '1',
            CEMASK  => '0',
            CLR     => '0',
            CLRMASK => '0',
            DIV     => "000",
            I       => gtrefclk_div
        );

       --IBUFDS_GTE2
       ibufds_gty_i: IBUFDS_GTE4
       generic map (
            REFCLK_EN_TX_PATH  => '0',
            REFCLK_HROW_CK_SEL => "01",
            REFCLK_ICNTL_RX    => "00"
        )
        port map (
            I     => REFCLK_P_IN,
            IB    => REFCLK_N_IN,
            CEB   => '0',
            O     => gtrefclk, -- 322.27 MHz
            ODIV2 => gtrefclk_div -- 161,135 Mhz
        );

    end generate;

    GEN_NO_CLKBUF: if (CLK_SLAVE) generate
        gtrefclk   <= REFCLK_IN;
        REFCLK_OUT <= gt0_txusrclk2_i;
    end generate;

    RXUSRCLK_BUFG_GT : BUFG_GT
    port map (
        O      =>  gt0_rxusrclk_i, -- 1-bit output: Buffer
        CE     => '1', -- 1-bit input: Buffer enable
        CEMASK => '0', -- 1-bit input: CE Mask
        CLR    => '0', -- 1-bit input: Asynchronous clear
        CLRMASK=> '0', -- 1-bit input: CLR Mask
        DIV    => "000", -- 3-bit input: Dymanic divide Value
        I      => gt0_rxoutclk_i
    );

    -- BUFG GT for driving RXUSRCLK2 ports of GT
    RXUSRCLK2_GT_BUFG_GT : BUFG_GT
    port map (
        O      => gt_rxusrclk2, -- 1-bit output: Buffer
        CE     => '1', -- 1-bit input: Buffer enable
        CEMASK => '0', -- 1-bit input: CE Mask
        CLR    => '0', -- 1-bit input: Asynchronous clear
        CLRMASK=> '0', -- 1-bit input: CLR Mask
        DIV    => "001", -- 3-bit input: Dymanic divide Value
        I      => gt0_rxoutclk_i
    );

    -- BUFG GT for driving FPGA logic
    RXUSRCLK2_FABRIC_BUFG_GT : BUFG_GT
    port map (
        O      =>  gt0_rxusrclk2_i, -- 1-bit output: Buffer
        CE     => '1', -- 1-bit input: Buffer enable
        CEMASK => '0', -- 1-bit input: CE Mask
        CLR    => '0', -- 1-bit input: Asynchronous clear
        CLRMASK=> '0', -- 1-bit input: CLR Mask
        DIV    => "001", -- 3-bit input: Dymanic divide Value
        I      => gt0_rxoutclk_i
    );

    TXUSRCLK_BUFG_GT : BUFG_GT
    port map (
        O      => gt0_txusrclk_i, -- 1-bit output: Buffer
        CE     => bufg_gt_ce(0), -- 1-bit input: Buffer enable
        CEMASK => '0', -- 1-bit input: CE Mask
        CLR    => '0', -- 1-bit input: Asynchronous clear
        CLRMASK=> '0', -- 1-bit input: CLR Mask
        DIV    => "000", -- 3-bit input: Dymanic divide Value
        I      => gt0_txoutclk_i
    );

    -- Bufer to drive GT USCLK2 pins
    TXUSRCLK2_BUFG_GT : BUFG_GT
    port map (
        O      => gt_txusrclk2, -- 1-bit output: Buffer
        CE     => bufg_gt_ce(0), -- 1-bit input: Buffer enable
        CEMASK => '0', -- 1-bit input: CE Mask
        CLR    => '0', -- 1-bit input: Asynchronous clear
        CLRMASK=> '0', -- 1-bit input: CLR Mask
        DIV    => "001", -- 3-bit input: Dymanic divide Value
        I      => gt0_txoutclk_i
    );

    -- The same bufer replicated to drive user logic
    TXUSRCLK2_BUFG_GT_FABRIC : BUFG_GT
    port map (
        O      => gt0_txusrclk2_i, -- 1-bit output: Buffer
        CE     => bufg_gt_ce(0), -- 1-bit input: Buffer enable
        CEMASK => '0', -- 1-bit input: CE Mask
        CLR    => '0', -- 1-bit input: Asynchronous clear
        CLRMASK=> '0', -- 1-bit input: CLR Mask
        DIV    => "001", -- 3-bit input: Dymanic divide Value
        I      => gt0_txoutclk_i
    );


    gt1_txusrclk_i    <= gt0_txusrclk_i;
    gt1_txusrclk2_i   <= gt0_txusrclk2_i;
    gt1_rxusrclk_i    <= gt0_rxusrclk_i;
    gt1_rxusrclk2_i   <= gt0_rxusrclk2_i;

    gt2_txusrclk_i    <= gt0_txusrclk_i;
    gt2_txusrclk2_i   <= gt0_txusrclk2_i;
    gt2_rxusrclk_i    <= gt0_rxusrclk_i;
    gt2_rxusrclk2_i   <= gt0_rxusrclk2_i;

    gt3_txusrclk_i    <= gt0_txusrclk_i;
    gt3_txusrclk2_i   <= gt0_txusrclk2_i;
    gt3_rxusrclk_i    <= gt0_rxusrclk_i;
    gt3_rxusrclk2_i   <= gt0_rxusrclk2_i;

    drpclk_in_i <= DRPCLK_IN;

    ----------------------------- The GT Wrapper -----------------------------

      -- Near-end PMA loopback only
    loopback_i  <= gt3_loopback_i & gt2_loopback_i & gt1_loopback_i & gt0_loopback_i;
    powerdown_i <= (others => POWERDOWN_IN);

    rxdata_ok_i <= RX_DATA_OK and ((gt3_block_lock_i and gt2_block_lock_i and gt1_block_lock_i and gt0_block_lock_i));
    gty_40ge_init_i: entity work.gt_init
    generic map (
        TX_TIMER_MAX  =>  3750000, -- ~ 30ms @ 125 MHz CLK
        RX_TIMER_MAX  => 16250000  -- ~130ms @ 125 MHz CLK
    )
    port map (
        CLK           => DRPCLK_IN,
        RESET         => RESET_IN,
        TX_INIT_DONE  => gtwiz_reset_tx_done,
        RX_INIT_DONE  => gtwiz_reset_rx_done,
        RX_DATA_OK    => (and BLK_LOCK_OUT),
        RESET_OUT     => reset_all_init,
        RXRESET_OUT   => reset_rx_datapath_init,
        INIT_DONE     => open
    );

    txusrrdy_ffs: process(txpmaresetdone, gt0_txusrclk2_i)
    begin
        if (and txpmaresetdone) = '0' then
            txusrrdy_meta <= '0';
            txusrrdy      <= '0';
        elsif rising_edge(gt0_txusrclk2_i) then
            txusrrdy_meta <= '1';
            txusrrdy      <= txusrrdy_meta;
        end if;
    end process;

    rxusrrdy_ffs: process(rxpmaresetdone, gt0_rxusrclk2_i)
    begin
        if (and rxpmaresetdone) = '0' then
            rxusrrdy_meta <= '0';
            rxusrrdy      <= '0';
        elsif rising_edge(gt0_rxusrclk2_i) then
            rxusrrdy_meta <= '1';
            rxusrrdy      <= rxusrrdy_meta;
        end if;
    end process;

    -- RX polarity clock domain crossing
    rxpol_sync_g: for i in RXPOLARITY'range generate
        rxpol_sync_i : entity work.ASYNC_OPEN_LOOP
        generic map(IN_REG  => false, TWO_REG => true)
        port map(ADATAIN  => RXPOLARITY(i), BCLK => gt_rxusrclk2, BRST => '0', BDATAOUT => gt_rxpolarity(i));
    end generate;

    txpol_sync_g: for i in TXPOLARITY'range generate
        txpol_sync_i : entity work.ASYNC_OPEN_LOOP
        generic map(IN_REG  => false, TWO_REG => true)
        port map(ADATAIN  => TXPOLARITY(i), BCLK => gt0_txusrclk2_i, BRST => '0', BDATAOUT => gt_txpolarity(i));
    end generate;

    gth_40gbaser_i: gty_40ge
    PORT map (
        gtwiz_userclk_tx_reset_in(0)       => '0',
        gtwiz_userclk_tx_active_in(0)      => txusrrdy,
        gtwiz_userclk_rx_active_in(0)      => rxusrrdy,
        gtwiz_reset_clk_freerun_in(0)      => DRPCLK_IN,
        drpclk_in                          => (others => DRPCLK_IN),
        --
        gtwiz_reset_all_in(0)              => (RESET_IN or reset_all_init),
        gtwiz_reset_tx_pll_and_datapath_in => (others => '0'),
        gtwiz_reset_tx_datapath_in         => (others => '0'),
        gtwiz_reset_rx_pll_and_datapath_in => (others => '0'),
        gtwiz_reset_rx_datapath_in(0)      => reset_rx_datapath_init,

        gtwiz_reset_rx_cdr_stable_out      => open,
        gtwiz_reset_tx_done_out(0)         => gtwiz_reset_tx_done,
        gtwiz_reset_rx_done_out(0)         => gtwiz_reset_rx_done,
        --
        gtwiz_gtye4_cpll_cal_txoutclk_period_in => "000001000000011101000001000000011101000001000000011101000001000000011101",
        gtwiz_gtye4_cpll_cal_cnt_tol_in         => "000000000000101001000000000000101001000000000000101001000000000000101001",
        gtwiz_gtye4_cpll_cal_bufg_ce_in         => bufg_gt_ce,
        --
        gtwiz_userdata_tx_in               => txdata_i,
        txheader_in                        => txheader_i,
        txsequence_in                      => txsequence_i,
        gtwiz_userdata_rx_out              => rxdata_i,
        rxheader_out                       => rxheader_i,
        rxdatavalid_out                    => rxdatavalid_i,
        rxheadervalid_out                  => rxheadervalid_i,
        rxgearboxslip_in                   => rxgearboxslip_i,
        --
        gtrefclk00_in(0)                   => gtrefclk,
        qpll0outclk_out                    => open, -- 5156.30 MHz
        qpll0outrefclk_out                 => open, -- 322.27 MHz
        --
        gtyrxn_in                          => RXN_IN,
        gtyrxp_in                          => RXP_IN,
        gtytxn_out                         => TXN_OUT,
        gtytxp_out                         => TXP_OUT,
        loopback_in                        => loopback_i,
        --
        rxpcsreset_in                      => (others => '0'),
        rxpolarity_in                      => gt_rxpolarity,
        rxpd_in                            => powerdown_i,
        rxpmareset_in                      => (others => '0'),
        rxpmaresetdone_out                 => rxpmaresetdone,
        rxresetdone_out                    => rxresetdone_i,
        --
        txpcsreset_in                      => (others => '0'),
        txpolarity_in                      => gt_txpolarity,
        txpmareset_in                      => (others => '0'),
        txpmaresetdone_out                 => txpmaresetdone,
        txresetdone_out                    => txresetdone_i,
        txpd_in                            => powerdown_i,
        gtpowergood_out                    => open,
        --
        rxoutclk_out(0)                    => gt0_rxoutclk_i,
        rxoutclk_out(1)                    => gt1_rxoutclk_i,
        rxoutclk_out(2)                    => gt2_rxoutclk_i,
        rxoutclk_out(3)                    => gt3_rxoutclk_i,
        txoutclk_out(0)                    => gt0_txoutclk_i,
        txoutclk_out(1)                    => gt1_txoutclk_i,
        txoutclk_out(2)                    => gt2_txoutclk_i,
        txoutclk_out(3)                    => gt3_txoutclk_i,
        rxusrclk_in(0)                     => gt0_rxusrclk_i,
        rxusrclk_in(1)                     => gt0_rxusrclk_i,
        rxusrclk_in(2)                     => gt0_rxusrclk_i,
        rxusrclk_in(3)                     => gt0_rxusrclk_i,
        rxusrclk2_in(0)                    => gt_rxusrclk2,
        rxusrclk2_in(1)                    => gt_rxusrclk2,
        rxusrclk2_in(2)                    => gt_rxusrclk2,
        rxusrclk2_in(3)                    => gt_rxusrclk2,
        txusrclk_in(0)                     => gt0_txusrclk_i,
        txusrclk_in(1)                     => gt0_txusrclk_i,
        txusrclk_in(2)                     => gt0_txusrclk_i,
        txusrclk_in(3)                     => gt0_txusrclk_i,
        txusrclk2_in(0)                    => gt_txusrclk2,
        txusrclk2_in(1)                    => gt_txusrclk2,
        txusrclk2_in(2)                    => gt_txusrclk2,
        txusrclk2_in(3)                    => gt_txusrclk2,
        rxprgdivresetdone_out              => open,
        txprgdivresetdone_out              => open,
        rxstartofseq_out                   => open
    );

    TXD_REGS: process(gt0_txusrclk2_i)
    begin
        if gt0_txusrclk2_i'event and gt0_txusrclk2_i = '1' then
            if gt0_txdatavalid_i = '1' then
                gt0_txheader_i  <= reverse(TXDATA_IN(0*66+1 downto 0*66+0));
                gt0_txdata_i    <= reverse(TXDATA_IN(1*66-1 downto 0*66+2));
                gt1_txheader_i  <= reverse(TXDATA_IN(1*66+1 downto 1*66+0));
                gt1_txdata_i    <= reverse(TXDATA_IN(2*66-1 downto 1*66+2));
                gt2_txheader_i  <= reverse(TXDATA_IN(2*66+1 downto 2*66+0));
                gt2_txdata_i    <= reverse(TXDATA_IN(3*66-1 downto 2*66+2));
                gt3_txheader_i  <= reverse(TXDATA_IN(3*66+1 downto 3*66+0));
                gt3_txdata_i    <= reverse(TXDATA_IN(4*66-1 downto 3*66+2));
            end if;
        end if;
    end process;

    txheader_i <= "0000" & gt3_txheader_i & "0000" & gt2_txheader_i & "0000" & gt1_txheader_i & "0000" & gt0_txheader_i;
    txdata_i   <= gt3_txdata_i & gt2_txdata_i & gt1_txdata_i & gt0_txdata_i;

    gt0_rxdata_i <= rxdata_i(1*64-1 downto 0*64);
    gt1_rxdata_i <= rxdata_i(2*64-1 downto 1*64);
    gt2_rxdata_i <= rxdata_i(3*64-1 downto 2*64);
    gt3_rxdata_i <= rxdata_i(4*64-1 downto 3*64);

    gt0_rxheader_i <= rxheader_i(0*6+1 downto 0*6);
    gt1_rxheader_i <= rxheader_i(1*6+1 downto 1*6);
    gt2_rxheader_i <= rxheader_i(2*6+1 downto 2*6);
    gt3_rxheader_i <= rxheader_i(3*6+1 downto 3*6);

    gt0_rxdatavalid_i <= rxdatavalid_i(0*2);
    gt1_rxdatavalid_i <= rxdatavalid_i(1*2);
    gt2_rxdatavalid_i <= rxdatavalid_i(2*2);
    gt3_rxdatavalid_i <= rxdatavalid_i(3*2);

    gt0_rxheadervalid_i <= rxheadervalid_i(0*2);
    gt1_rxheadervalid_i <= rxheadervalid_i(1*2);
    gt2_rxheadervalid_i <= rxheadervalid_i(2*2);
    gt3_rxheadervalid_i <= rxheadervalid_i(3*2);

    OUT_REGS: process(gt0_rxusrclk2_i)
    begin
        if gt0_rxusrclk2_i'event and gt0_rxusrclk2_i = '1' then
            rxdata_ff(0*66+1 downto 0*66)  <= reverse(gt0_rxheader_i);
            rxdata_ff(1*66-1 downto 0*66+2)<= reverse(gt0_rxdata_i);
            rxdata_ff(1*66+1 downto 1*66)  <= reverse(gt1_rxheader_i);
            rxdata_ff(2*66-1 downto 1*66+2)<= reverse(gt1_rxdata_i);
            rxdata_ff(2*66+1 downto 2*66)  <= reverse(gt2_rxheader_i);
            rxdata_ff(3*66-1 downto 2*66+2)<= reverse(gt2_rxdata_i);
            rxdata_ff(3*66+1 downto 3*66)  <= reverse(gt3_rxheader_i);
            rxdata_ff(4*66-1 downto 3*66+2)<= reverse(gt3_rxdata_i);

            rxvalid_ff(0) <= gt0_rxheadervalid_i and gt0_rxdatavalid_i;
            rxvalid_ff(1) <= gt1_rxheadervalid_i and gt1_rxdatavalid_i;
            rxvalid_ff(2) <= gt2_rxheadervalid_i and gt2_rxdatavalid_i;
            rxvalid_ff(3) <= gt3_rxheadervalid_i and gt3_rxdatavalid_i;
       end if;
    end process;

    RXDATA_OUT  <= rxdata_ff;
    RXVALID_OUT <= rxvalid_ff;

    -- =========================================================================
    -- Block sync logic
    -- =========================================================================
    TXREADY_OUT(0) <= gt0_txdatavalid_i;
    TXREADY_OUT(1) <= gt1_txdatavalid_i;
    TXREADY_OUT(2) <= gt2_txdatavalid_i;
    TXREADY_OUT(3) <= gt3_txdatavalid_i;

    txsequence_i <= (others => '0');

    gt0_txdatavalid_i <= '1';
    gt1_txdatavalid_i <= '1';
    gt2_txdatavalid_i <= '1';
    gt3_txdatavalid_i <= '1';

    BLK_LOCK_OUT(0) <= gt0_block_lock_i;
    BLK_LOCK_OUT(1) <= gt1_block_lock_i;
    BLK_LOCK_OUT(2) <= gt2_block_lock_i;
    BLK_LOCK_OUT(3) <= gt3_block_lock_i;

    block_sync_sm_0_i  : entity work.BLOCK_LOCK
    generic map (
        SH_CNT_MAX          => 1024,
        SH_INVALID_CNT_MAX  => 64
    )
    port map (
        RX_HEADER_IN        => gt0_rxheader_i,
        RX_HEADER_VALID     => gt0_rxheadervalid_i,
        CLK                 => gt0_rxusrclk2_i,
        RST                 => gt0_rx_reset_i,
        RX_LOCK_AQUIRED     => gt0_block_lock_i,
        SLIP_CMD            => gt0_rxgearboxslip_i
    );

    block_sync_sm_1_i  : entity work.BLOCK_LOCK
    generic map (
        SH_CNT_MAX          => 1024,
        SH_INVALID_CNT_MAX  => 64
    )
    port map (
        RX_HEADER_IN        => gt1_rxheader_i,
        RX_HEADER_VALID     => gt1_rxheadervalid_i,
        CLK                 => gt1_rxusrclk2_i,
        RST                 => gt1_rx_reset_i,
        RX_LOCK_AQUIRED     => gt1_block_lock_i,
        SLIP_CMD            => gt1_rxgearboxslip_i
    );

    block_sync_sm_2_i  : entity work.BLOCK_LOCK
    generic map (
        SH_CNT_MAX          => 1024,
        SH_INVALID_CNT_MAX  => 64
    )
    port map (
        RX_HEADER_IN        => gt2_rxheader_i,
        RX_HEADER_VALID     => gt2_rxheadervalid_i,
        CLK                 => gt2_rxusrclk2_i,
        RST                 => gt2_rx_reset_i,
        RX_LOCK_AQUIRED     => gt2_block_lock_i,
        SLIP_CMD            => gt2_rxgearboxslip_i
    );

    block_sync_sm_3_i  : entity work.BLOCK_LOCK
    generic map (
        SH_CNT_MAX          => 1024,
        SH_INVALID_CNT_MAX  => 64
    )
    port map (
        RX_HEADER_IN        => gt3_rxheader_i,
        RX_HEADER_VALID     => gt3_rxheadervalid_i,
        CLK                 => gt3_rxusrclk2_i,
        RST                 => gt3_rx_reset_i,
        RX_LOCK_AQUIRED     => gt3_block_lock_i,
        SLIP_CMD            => gt3_rxgearboxslip_i
    );

    rxgearboxslip_i <= gt3_rxgearboxslip_i & gt2_rxgearboxslip_i & gt1_rxgearboxslip_i & gt0_rxgearboxslip_i;

    -------------------------------------------------------------------------------

    TXCLK_OUT    <= gt0_txusrclk2_i;
    RXCLK_OUT    <= gt0_rxusrclk2_i;
    TXCLK_STABLE <= txresetdone_i(0);
    RXCLK_STABLE <= rxresetdone_i(0);

    DATA_TOGGLE_DETECTOR: process(gt0_rxusrclk2_i)
    begin
        if gt0_rxusrclk2_i'event and gt0_rxusrclk2_i = '1' then
            if (gt0_rxdatavalid_i = '1') and (rxvalid_ff(0) = '1') then
                if gt0_rxdata_i /= rxdata_ff(66*1-1 downto 66*0+2) then
                    rx_toggle_counter0 <= (others => '0');
                elsif rx_toggle_counter0(rx_toggle_counter0'high) = '0' then
                    rx_toggle_counter0 <= rx_toggle_counter0 + 1;
                end if;
            end if;

            if (gt1_rxdatavalid_i = '1') and (rxvalid_ff(1) = '1') then
                if gt1_rxdata_i /= rxdata_ff(66*2-1 downto 66*1+2) then
                    rx_toggle_counter1 <= (others => '0');
                elsif rx_toggle_counter1(rx_toggle_counter1'high) = '0' then
                    rx_toggle_counter1 <= rx_toggle_counter1 + 1;
                end if;
            end if;

            if (gt2_rxdatavalid_i = '1') and (rxvalid_ff(2) = '1') then
                if gt2_rxdata_i /= rxdata_ff(66*3-1 downto 66*2+2) then
                    rx_toggle_counter2 <= (others => '0');
                elsif rx_toggle_counter2(rx_toggle_counter2'high) = '0' then
                    rx_toggle_counter2 <= rx_toggle_counter2 + 1;
                end if;
            end if;

            if (gt3_rxdatavalid_i = '1') and (rxvalid_ff(3) = '1') then
                if gt3_rxdata_i /= rxdata_ff(66*4-1 downto 66*3+2) then
                    rx_toggle_counter3 <= (others => '0');
                elsif rx_toggle_counter3(rx_toggle_counter3'high) = '0' then
                    rx_toggle_counter3 <= rx_toggle_counter3 + 1;
                end if;
            end if;

        end if;
    end process;

    rx_init_done <=  rxresetdone_i(3) and rxresetdone_i(2) and rxresetdone_i(1) and rxresetdone_i(0);

    rxdata0_toggle <= not rx_toggle_counter0(rx_toggle_counter0'high) or RXDETECT_BYPASS;
    rxdata1_toggle <= not rx_toggle_counter1(rx_toggle_counter1'high) or RXDETECT_BYPASS;
    rxdata2_toggle <= not rx_toggle_counter2(rx_toggle_counter2'high) or RXDETECT_BYPASS;
    rxdata3_toggle <= not rx_toggle_counter3(rx_toggle_counter3'high) or RXDETECT_BYPASS;

    RX_OK <= rxresetdone_i(3) & rxresetdone_i(2) & rxresetdone_i(1) & rxresetdone_i(0);

    tx_resetdone_i  <=   txresetdone_i(3) and
                         txresetdone_i(2) and
                         txresetdone_i(1) and
                         txresetdone_i(0);

    TXRESET_DONE_OUT <= tx_resetdone_i;

    RXRESET_DONE_OUT <=  rxresetdone_i(3) and
                         rxresetdone_i(2) and
                         rxresetdone_i(1) and
                         rxresetdone_i(0);

    gt0_tx_system_reset_c <= not txresetdone_i(0);
    gt1_tx_system_reset_c <= not txresetdone_i(1);
    gt2_tx_system_reset_c <= not txresetdone_i(2);
    gt3_tx_system_reset_c <= not txresetdone_i(3);

    gt0_rx_system_reset_c <= not rx_init_done or (not rxdata0_toggle);
    gt1_rx_system_reset_c <= not rx_init_done or (not rxdata1_toggle);
    gt2_rx_system_reset_c <= not rx_init_done or (not rxdata2_toggle);
    gt3_rx_system_reset_c <= not rx_init_done or (not rxdata3_toggle);

    sync_gt0_rx_reset_i: entity work.ASYNC_RESET
    generic map(
       TWO_REG => false -- For two reg = true, for three reg = false
    )
    port map(
       CLK        => gt0_rxusrclk2_i,
       ASYNC_RST  => gt0_rx_system_reset_c,
       OUT_RST(0) => gt0_rx_reset_i
    );

    sync_gt1_rx_reset_i: entity work.ASYNC_RESET
    generic map(
       TWO_REG => false -- For two reg = true, for three reg = false
    )
    port map(
       CLK        => gt1_rxusrclk2_i,
       ASYNC_RST  => gt1_rx_system_reset_c,
       OUT_RST(0) => gt1_rx_reset_i
    );

    sync_gt2_rx_reset_i: entity work.ASYNC_RESET
    generic map(
       TWO_REG => false -- For two reg = true, for three reg = false
    )
    port map(
       CLK        => gt2_rxusrclk2_i,
       ASYNC_RST  => gt2_rx_system_reset_c,
       OUT_RST(0) => gt2_rx_reset_i
    );

    sync_gt3_rx_reset_i: entity work.ASYNC_RESET
    generic map(
       TWO_REG => false -- For two reg = true, for three reg = false
    )
    port map(
       CLK        => gt3_rxusrclk2_i,
       ASYNC_RST  => gt3_rx_system_reset_c,
       OUT_RST(0) => gt3_rx_reset_i
    );

    gt0_loopback_i                               <= LOOPBACK_IN;
    gt1_loopback_i                               <= LOOPBACK_IN;
    gt2_loopback_i                               <= LOOPBACK_IN;
    gt3_loopback_i                               <= LOOPBACK_IN;

-------------------------------------------------------------------------------

end usp_gty;
