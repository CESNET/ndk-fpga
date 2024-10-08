-- mgmt.vhd : 40/100GBASE-R management (status/control)
-- Copyright (C) 2011 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
--            Jakub Cabal   <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- NOTES:
-- Address space is similar to standard MDIO register mapping, while the lower
-- 16 address bits are register number, upper 5 bits are device (1=PMA, 3=PCS)
-- Detailed address space:
-- PMA:
-- MI address  upper 16b  &  lower 16b
-- 0x10000    PMA status1 & control1
-- 0x10004    PMA device identifier 2 & 1
-- 0x10008    PMA devices in package & speed capability
-- ...
--
-- 1.0      PMA/PMD control 1
-- 1.1      PMA/PMD status 1
-- 1.2, 1.3 PMA/PMD device identifier
-- 1.4      PMA/PMD speed ability
-- 1.5, 1.6 PMA/PMD devices in package
-- 1.7      PMA/PMD control 2
-- 1.8      PMA/PMD status 2
-- 1.9      PMA/PMD transmit disable
-- 1.10     PMD receive signal detect
-- 1.11     PMA/PMD extended ability register
-- 1.12     10G-EPON PMA/PMD P2MP ability register 45.2.1.11
-- 1.13     40G/100G PMA/PMD extended ability register 45.2.1.11a
-- 1.14,1.15 PMA/PMD package identifier
-- 1.1500    Test pattern ability 45.2.1.95
-- 1.1501    PRBS pattern testing control 45.2.1.96
-- 1.1510    Square wave testing control 45.2.1.97
-- 1.1600 - 1609 PRBS Tx error counters, lane 0 through lane 9 45.2.1.98
-- 1.1700 - 1709 PRBS Rx error counters, lane 0 through lane 9 45.2.1.99
--  Vendor specific PMA controls:
-- 0x18000 -- PMA specific control
-- 0x18004 -- PMA specific status
-- 0x18008 -- RS-FEC RX & TX enable
-- 0x18020 -- PMA TX swing (TX differential driver swing)
-- 0x18024 -- PMA TX preemphasis control - precursor
-- 0x18028 -- PMA TX preemphasis control - postcursor
-- 0x18010: DRP data
-- 0x18014: DRP address
-- 0x18018:   [0]: operation type (R/W). Bit is write only
--          [7:4]: DRP page select. Write only
--           [31]: '1' = DRP read operation in progress; '0' = DRP data ready. Read only
--          Write to this register starts the DPR operation
-- PCS:
--   TODO

library ieee;
use ieee.std_logic_1164.all;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

entity mgmt is
   generic (
      -- Number of PCS lanes. Max 20
      NUM_LANES : natural range 0 to 20 := 4;
      -- Max 10
      PMA_LANES : natural range 0 to 10 := 4;
      -- Current PMA/PCS speed. Replaces SPEEDxx when not zero
      SPEED     : natural := 0;
      -- Speed capabilities, see 802.3 table 45-6. Replaces GBASExx_ABLE when not zero.
      SPEED_CAP : std_logic_vector(15 downto 0) := X"0000";
      -- Speed is 100G when '1'
      SPEED100G     : std_logic := '0';
      -- Speed is 10G  when '1'
      SPEED10G      : std_logic := '0';
      -- 40GE capable
      GBASE40_ABLE  : std_logic := '1';
      -- 100GE capable
      GBASE100_ABLE : std_logic := '0';
      -- RS-FEC capable
      RSFEC_ABLE    : std_logic := '0';
      -- Auto-negotiation capable
      AN_ABLE       : std_logic := '0';
      -- Default value of FEC_EN (must be set '1' when the RSFEC is enabled at poweron or reset)
      RSFEC_EN_INIT : std_logic := '0';
      -- PMA_CONTROL power-up and reset defaults
      PMA_CONTROL_INIT    : std_logic_vector(31 downto 0) := (others => '0');
      PMA_PRECURSOR_INIT  : std_logic_vector(31 downto 0) := (others => '0');
      PMA_POSTCURSOR_INIT : std_logic_vector(31 downto 0) := (others => '0');
      PMA_DRIVE_INIT      : std_logic_vector(31 downto 0) := (others => '0');
      -- Width of the DRP data
      DRP_DWIDTH          : natural := 16;
      -- Width of the DRP address
      DRP_AWIDTH          : natural := 16;
      -- Select correct FPGA device.
      -- "AGILEX", "STRATIX10", "ULTRASCALE", ...
      DEVICE : string  := "ULTRASCALE"
   );
   port (
      RESET       : in  std_logic;
      -- =====================================================================
      -- MI32 interface
      -- =====================================================================

      MI_CLK      : in  std_logic;
      MI_DWR      : in  std_logic_vector(31 downto 0);
      MI_ADDR     : in  std_logic_vector(31 downto 0);
      MI_RD       : in  std_logic;
      MI_WR       : in  std_logic;
      MI_BE       : in  std_logic_vector( 3 downto 0);
      MI_DRD      : out std_logic_vector(31 downto 0);
      MI_ARDY     : out std_logic;
      MI_DRDY     : out std_logic;

      -- =====================================================================
      -- PCS and PMA CLK
      --
      -- Following clock are unused - left for interface compatibility only
      -- =====================================================================

      -- PCS clock (156.25MHz)
      PCSCLK      : in  std_logic := '0';
      -- PMA clock (159.xxMHz)
      PMACLK      : in  std_logic := '0';

      -- =====================================================================
      -- PCS control/status
      -- =====================================================================

      -- BER monitor HI BER
      HI_BER        : in std_logic;
      -- Block sync lock for each lane
      BLK_LOCK      : in std_logic_vector(NUM_LANES-1 downto 0);
      -- RX link status (=aligned and !hi_ber)
      LINKSTATUS    : in std_logic;
      -- BER monitor number of errored blocks for each lane
      BER_COUNT     : in std_logic_vector(21 downto 0);
      -- Clear block count in the block sync
      BER_COUNT_CLR : out std_logic;
      -- Block decode error counter
      BLK_ERR_CNTR  : in  std_logic_vector(21 downto 0);
      -- Clear errored block counter in the decoder
      BLK_ERR_CLR   : out std_logic;
      -- Bypass the RX scrambler (bit 0) and TX scrambler (bit 1) - MI_CLK domain
      SCR_BYPASS    : out std_logic_vector(1 downto 0);
      -- Reset the PCS block
      PCS_RESET     : out std_logic;
      -- PCS loopback enable
      PCS_LPBCK     : out std_logic;
      -- Lane align
      ALGN_LOCKED   : in  std_logic;
      -- BIP error counters
      BIP_ERR_CNTRS : in  std_logic_vector(NUM_LANES*16-1 downto 0);
      -- Clear BIP error counter for individual lane
      BIP_ERR_CLR   : out std_logic_vector(NUM_LANES-1 downto 0);
      -- PCS lane mapping
      LANE_MAP      : in  std_logic_vector(NUM_LANES*5-1 downto 0);
      -- PCS lane align for individual lanes
      LANE_ALIGN    : in  std_logic_vector(NUM_LANES-1 downto 0);
      -- PCS vendor specific control register (3.4000)
      PCS_CONTROL   : out std_logic_vector(16-1 downto 0);
      -- PCS vendor specific control register (3.4000)
      PCS_CONTROL_I : in std_logic_vector(16-1 downto 0) := (others => '0');
      -- PCS vendor specific control readback (3.4000) + status (3.4001) register
      PCS_STATUS    : in  std_logic_vector(16-1 downto 0) := (others => '0');

      -- =====================================================================
      -- PMA control
      -- =====================================================================

      -- Turn the PMA into lo-power state
      PMA_LOPWR     : out std_logic;
      PMA_LPBCK     : out std_logic;
      PMA_REM_LPBCK : out std_logic;
      PMA_RESET     : out std_logic;
      PMA_RETUNE    : out std_logic;
      -- Vendor specific PMA control
      PMA_CONTROL   : out std_logic_vector(31 downto 0);
      -- Vendor specific PMA status: startup FSM states
      PMA_STATUS    : in  std_logic_vector(31 downto 0) := (others => '0');
      -- Pattern generator enable
      PMA_PTRN_EN   : out std_logic := '0';
      -- PMA transmitt disable for individual lanes
      PMA_TX_DIS    : out std_logic_vector(PMA_LANES-1 downto 0);
      -- PMA RX link ok
      PMA_RX_OK     : in  std_logic_vector(PMA_LANES-1 downto 0);
      PMD_SIG_DET   : in  std_logic_vector(PMA_LANES-1 downto 0);
      -- TX driver precursor for preemphasis control
      PMA_PRECURSOR : out std_logic_vector(31 downto 0);
      -- TX driver postcursor for preemphasis control
      PMA_POSTCURSOR: out std_logic_vector(31 downto 0);
      -- TX driver swing control
      PMA_DRIVE     : out std_logic_vector(31 downto 0);

      -- =====================================================================
      -- Clause 91 RS-FEC control/status
      -- =====================================================================

      FEC_TX_EN     :  out std_logic;
      FEC_RX_EN     :  out std_logic;
      -- FEC correction enable
      FEC_COR_EN    :  out std_logic;
      -- FEC error indication enable
      FEC_IND_EN    :  out std_logic;
      FEC_AM_LOCK   :  in  std_logic_vector(4-1 downto 0) := (others => '0');
      FEC_HI_SER    :  in  std_logic := '0';
      FEC_ALGN_STAT :  in  std_logic := '0';
      -- 1.206:     RS-FEC lane mapping
      FEC_LANE_MAP  :  in  std_logic_vector(7 downto 0) := (others => '0');
      -- 1.210-207: Symbol error conters for lane 0-3
      FEC_SYM_ERR       :  in  std_logic_vector(4*32-1 downto 0) := (others => '0');
      -- Clear the counters
      FEC_SYM_ERR_CLR   :  out std_logic_vector(3 downto 0);
      -- 1.202,203: RS-FEC corrected codewords counter
      FEC_COR_ERR       :  in  std_logic_vector(32-1 downto 0) := (others => '0');
      -- Clear the counter
      FEC_COR_ERR_CLR   :  out std_logic;
      -- 1.204,205: RS-FEC uncorrected codewords counter
      FEC_UNCOR_ERR     :  in  std_logic_vector(32-1 downto 0) := (others => '0');
      -- Clear the counter
      FEC_UNCOR_ERR_CLR :  out std_logic;
      -- 1.230-249: RS-FEC BIP error counters, lane 0 to 19
      FEC_TX_BIP        :  in  std_logic_vector(16*20-1 downto 0) := (others => '0');
      -- 1.250-269: RS-FEC PCS lane mapping, lane 0 to 19
      FEC_TX_LANE_MAP   :  in  std_logic_vector(16*20-1 downto 0) := (others => '0');
      -- 1.280-281: RS-FEC PCS alignment status 1 through 4
      FEC_TX_BLK_LOCK   :  in  std_logic_vector(20-1 downto 0) := (others => '0');
      -- 1.282-283: RS-FEC PCS alignment status 3 through 4
      FEC_TX_ALGN_STAT  :  in  std_logic_vector(20-1 downto 0) := (others => '0');

      -- =====================================================================
      -- DRP interface for transceivers etc.
      -- =====================================================================
      DRPCLK            : in  std_logic := '0';
      DRPDO             : in  std_logic_vector(DRP_DWIDTH-1 downto 0) := (others => '0');
      DRPRDY            : in  std_logic := '0';
      DRPEN             : out std_logic;
      DRPWE             : out std_logic;
      DRPADDR           : out std_logic_vector(DRP_AWIDTH-1 downto 0);
      DRPARDY           : in  std_logic := '1';
      DRPDI             : out std_logic_vector(DRP_DWIDTH-1 downto 0);
      DRPSEL            : out std_logic_vector(3 downto 0)
   );
end mgmt;

architecture behavioral of mgmt is

signal mi_addr_masked : std_logic_vector(31 downto 0);
signal mi_drd_i     : std_logic_vector(31 downto 0);
signal pma_mode     : std_logic_vector(6 downto 0);
signal pma_mode_set : std_logic_vector(6 downto 0);
signal pma_fault    : std_logic;
signal pma_rxl_stat : std_logic;
signal pma_rst      : std_logic := '0';
signal pcs_fault    : std_logic;
signal pcs_fault_l  : std_logic;
signal pcs_rxl_stat : std_logic;
signal pcs_rxl_stat_l : std_logic;
signal pcs_rst      : std_logic := '0';
signal pcs_lpbk     : std_logic := '0';
signal pcs_low_pwr  : std_logic := '0';
signal pcs_blk_lock_g : std_logic;
signal pcs_blk_lock_l : std_logic; -- latched version
signal pcs_hi_ber   : std_logic;
signal pcs_hi_ber_l : std_logic; -- latched version
signal pcs_blk_lock : std_logic_vector(19 downto 0);
signal ber_count_r  : std_logic_vector(21 downto 0);
signal blk_err_cntr_r : std_logic_vector(21 downto 0);
signal ber_count_l    : std_logic_vector(15 downto 0);
signal blk_err_cntr_l : std_logic_vector(13 downto 0);
signal tx_fault     : std_logic; -- latching
signal rx_fault     : std_logic; -- latching
signal low_pwr      : std_logic := '0';
signal pma_rem_lpbk : std_logic := '0';
signal pma_loc_lpbk : std_logic := '0';
signal tx_dis       : std_logic_vector(9 downto 0) := (others => '0');
signal tx_dis_g     : std_logic; -- global PMD TX disable
signal rx_sig_det   : std_logic_vector(9 downto 0);
signal rx_sig_det_g : std_logic; -- global signal detect
signal bip_ercntr_r : std_logic_vector(20*16-1 downto 0);
signal lane_map_i   : std_logic_vector(20*5-1 downto 0);
signal lane_align_i : std_logic_vector(20-1 downto 0);
signal scr_bypass_r : std_logic_vector(1 downto 0); --
signal r333_rd      : std_logic; -- register rx.yy read
signal r333_rd_r    : std_logic; -- register rx.yy read registred
signal r301_rd      : std_logic; -- register rx.yy read
signal r301_rd_r    : std_logic; -- register rx.yy read registred
signal r308_rd      : std_logic; -- register rx.yy read
signal r308_rd_r    : std_logic; -- register rx.yy read registred
signal r3200_rd     : std_logic_vector(19 downto 0); -- register r3.200..219 read
signal r3200_rd_r   : std_logic_vector(19 downto 0); -- register r3.200..219 read
signal r1201_rd     : std_logic; -- register rx.yyy read
signal r1203_rd     : std_logic; -- register rx.yyy read
signal r1205_rd     : std_logic; -- register rx.yyy read
signal r1211_rd     : std_logic; -- register rx.yyy read
signal r1213_rd     : std_logic; -- register rx.yyy read
signal r1215_rd     : std_logic; -- register rx.yyy read
signal r1217_rd     : std_logic; -- register rx.yyy read
signal r1201_rd_r   : std_logic; -- register rx.yyy read registred
signal r1203_rd_r   : std_logic; -- register rx.yyy read registred
signal r1205_rd_r   : std_logic; -- register rx.yyy read registred
signal r1211_rd_r   : std_logic; -- register rx.yyy read registred
signal r1213_rd_r   : std_logic; -- register rx.yyy read registred
signal r1215_rd_r   : std_logic; -- register rx.yyy read registred
signal r1217_rd_r   : std_logic; -- register rx.yyy read registred
-- reset signals
signal async_rst_mi                : std_logic;
-- cross domain crossing signals
signal reclock_from_pma_to_mi      : std_logic_vector(NUM_LANES*23+24 downto 0);
signal sync_reclock_from_pma_to_mi : std_logic_vector(NUM_LANES*23+24 downto 0);
signal sync_algn_locked            : std_logic;
signal sync_blk_lock               : std_logic_vector(NUM_LANES-1 downto 0);
signal sync_lane_align             : std_logic_vector(NUM_LANES-1 downto 0);
signal sync_lane_map               : std_logic_vector(NUM_LANES*5-1 downto 0);
signal sync_bip_err_cntrs          : std_logic_vector(NUM_LANES*16-1 downto 0);
signal sync_pma_rx_ok              : std_logic_vector(PMA_RX_OK'range);
signal sync_pmd_sig_det            : std_logic_vector(PMD_SIG_DET'range);
signal sync_pcs_status             : std_logic_vector(PCS_STATUS'range);
signal sync_pcs_control            : std_logic_vector(PCS_CONTROL_I'range);
signal mi_bip_err_clr              : std_logic_vector(NUM_LANES-1 downto 0);
signal pma_control_r               : std_logic_vector(PMA_CONTROL'range) := PMA_CONTROL_INIT;
signal pma_status_sync             : std_logic_vector(PMA_STATUS'range);
signal pma_precursor_r             : std_logic_vector(PMA_CONTROL'range) := PMA_PRECURSOR_INIT;
signal pma_postcursor_r            : std_logic_vector(PMA_CONTROL'range) := PMA_POSTCURSOR_INIT;
signal pma_drive_r                 : std_logic_vector(PMA_CONTROL'range) := PMA_DRIVE_INIT;
-- RS-FEC control/status
signal fec_tx_en_r                 : std_logic := '1'; -- TX FEC enable
signal fec_rx_en_r                 : std_logic := '1'; -- RX FEC enable
signal fec_en_r                    : std_logic := RSFEC_EN_INIT; -- RX FEC enable
signal fec_ind_bypass_r            : std_logic; -- FEC bypass indication
signal fec_cor_bypass_r            : std_logic; -- FEC bypass correction
signal FEC_AM_LOCK_sync            : std_logic_vector(FEC_AM_LOCK'range);
signal FEC_HI_SER_sync             : std_logic;
signal fec_hi_ser_l                : std_logic; -- High SER latched
signal FEC_ALGN_STAT_sync          : std_logic;
signal FEC_LANE_MAP_sync           : std_logic_vector(FEC_LANE_MAP'range);
signal FEC_sym_ERR_sync             : std_logic_vector(FEC_SYM_ERR'range);
signal FEC_COR_ERR_sync            : std_logic_vector(FEC_COR_ERR'range);
signal FEC_UNCOR_ERR_sync          : std_logic_vector(FEC_UNCOR_ERR'range);
signal FEC_TX_BIP_sync             : std_logic_vector(FEC_TX_BIP'range);
signal FEC_TX_LANE_MAP_sync        : std_logic_vector(FEC_TX_LANE_MAP'range);
signal FEC_TX_BLK_LOCK_sync        : std_logic_vector(FEC_TX_BLK_LOCK'range);
signal FEC_TX_ALGN_STAT_sync       : std_logic_vector(FEC_TX_ALGN_STAT'range);
signal fec_pcs_algn_stat            : std_logic;
-- DRP signals
signal drpdo_r       : std_logic_vector(DRPDO'range);
signal drpen_i       : std_logic;
signal drpwe_r       : std_logic;
signal drpaddr_r     : std_logic_vector(DRPADDR'range);
signal drpdi_r       : std_logic_vector(DRPDI'range);
signal drpsel_r      : std_logic_vector(DRPSEL'range);
signal drp_drd_sync  : std_logic_vector(DRPDO'range);
signal drp_drdy_sync : std_logic;
signal drp_rd        : std_logic;
signal drp_wr        : std_logic;
signal drpbusy_r     : std_logic;
signal drpbusy       : std_logic;
signal speed_int     : natural;
signal speed_cap_int : std_logic_vector(15 downto 0);

alias SPEED_CAP_10G  : std_logic is speed_cap_int(0);
alias SPEED_CAP_25G  : std_logic is speed_cap_int(11);
alias SPEED_CAP_40G  : std_logic is speed_cap_int(8);
alias SPEED_CAP_50G  : std_logic is speed_cap_int(3);
alias SPEED_CAP_100G : std_logic is speed_cap_int(9);
alias SPEED_CAP_200G : std_logic is speed_cap_int(12);
alias SPEED_CAP_400G : std_logic is speed_cap_int(15);

-- Requested PMA mode (software attempts to set this mode)
alias pm_req    : std_logic_vector(2 downto 0) is MI_DWR(18 downto 16);
alias pm_req_hi : std_logic_vector(3 downto 0) is MI_DWR(22 downto 19);

function AND_REDUCE (D : in std_logic_vector) return std_logic is
variable tmp : std_logic;
begin
   tmp := D(0);
   for i in 1 to D'high loop
      tmp := tmp and D(i);
   end loop;
   return tmp;
end function AND_REDUCE;

function OR_REDUCE (D : in std_logic_vector) return std_logic is
variable tmp : std_logic;
begin
   tmp := D(0);
   for i in 1 to D'high loop
      tmp := tmp or D(i);
   end loop;
   return tmp;
end function OR_REDUCE;

begin

speed_int <= SPEED when SPEED /= 0 else
             100   when SPEED100G = '1' else
             10    when SPEED10G  = '1' else
             40;

-- PMA speed capabilities - IEEE 802.3 Table 45-6
-- Bit 0: 10G, Bit 3: 50G, Bit 8: 40G, Bit 9: 100G, Bit 11: 25G, Bit 12: 200G, Bit 15: 400G
speed_cap_int <= SPEED_CAP when (SPEED_CAP /= X"0000") else
                 "000000" & GBASE100_ABLE & GBASE40_ABLE & "0000000" & SPEED10G;

fec_pcs_algn_stat <= and_reduce(FEC_TX_BLK_LOCK_sync) and and_reduce(FEC_TX_ALGN_STAT_sync);

-- SYNCHRONIZATION RESET SIGNALS
---------------------------------------------------
SYNC_RST_TO_MICLK: entity work.ASYNC_RESET
generic map(
   TWO_REG => false -- For two reg = true, for three reg = false
)
port map(
   CLK        => MI_CLK,
   ASYNC_RST  => RESET,
   OUT_RST(0) => async_rst_mi -- reclocked global async reset
);

-- INPUT CLOCK DOMAIN CROSSING FROM PMA TO MI
---------------------------------------------------

CROSS_HI_BER: entity work.ASYNC_OPEN_LOOP
generic map(IN_REG  => false, TWO_REG => true)
port map(
   ACLK     => '0',
   ARST     => '0',
   ADATAIN  => HI_BER,
   --
   BCLK     => MI_CLK,
   BRST     => '0',
   BDATAOUT => pcs_hi_ber
);

CROSS_LNKSTAT: entity work.ASYNC_OPEN_LOOP
generic map(IN_REG  => false, TWO_REG => true)
port map(
   ACLK     => '0',
   ARST     => '0',
   ADATAIN  => LINKSTATUS,
   --
   BCLK     => MI_CLK,
   BRST     => '0',
   BDATAOUT => pcs_rxl_stat
);

GEN_BER_CROSS: for i in 0 to BER_COUNT'high generate
   CROSS_BERCOUNT: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map (
      ACLK     => '0',
      ARST     => '0',
      ADATAIN  => BER_COUNT(i),
      --
      BCLK     => MI_CLK,
      BRST     => '0',
      BDATAOUT => ber_count_r(i)
   );
end generate;

GEN_BLKLOCK_CROSS: for i in 0 to BLK_LOCK'high generate
   CROSS_BLKLOCK: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map (
      ACLK     => '0',
      ARST     => '0',
      ADATAIN  => BLK_LOCK(i),
      --
      BCLK     => MI_CLK,
      BRST     => '0',
      BDATAOUT => sync_blk_lock(i)
   );
end generate;

GEN_SINGLELANE_STATS: if (NUM_LANES = 1) generate

   sync_algn_locked <= '1';

end generate;

GEN_MULTILANE_STATS: if (NUM_LANES > 1) generate

CROSS_ALOCK: entity work.ASYNC_OPEN_LOOP
generic map(IN_REG  => false, TWO_REG => true)
port map(
   ACLK     => '0',
   ARST     => '0',
   ADATAIN  => ALGN_LOCKED,
   --
   BCLK     => MI_CLK,
   BRST     => '0',
   BDATAOUT => sync_algn_locked
);

GEN_LA_CROSS: for i in 0 to LANE_ALIGN'high generate
   CROSS_LA: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map (
      ACLK     => '0',
      ARST     => '0',
      ADATAIN  => LANE_ALIGN(i),
      --
      BCLK     => MI_CLK,
      BRST     => '0',
      BDATAOUT => sync_lane_align(i)
   );
end generate;

GEN_LM_CROSS: for i in 0 to LANE_MAP'high generate
   CROSS_LM: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map (
      ACLK     => '0',
      ARST     => '0',
      ADATAIN  => LANE_MAP(i),
      --
      BCLK     => MI_CLK,
      BRST     => '0',
      BDATAOUT => sync_lane_map(i)
   );
end generate;

GEN_BIPER_CROSS: for i in 0 to BIP_ERR_CNTRS'high generate
   CROSS_BIPER: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map (
      ACLK     => '0',
      ARST     => '0',
      ADATAIN  => BIP_ERR_CNTRS(i),
      --
      BCLK     => MI_CLK,
      BRST     => '0',
      BDATAOUT => sync_bip_err_cntrs(i)
   );
end generate;

end generate; -- if NUM_LANES>1

-- INPUT CLOCK DOMAIN CROSSING FROM PCS TO MI
---------------------------------------------------

GEN_BLKER_CROSS: for i in BLK_ERR_CNTR'range generate
   CROSS_BLKER: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map (
      ACLK     => '0',
      ARST     => '0',
      ADATAIN  => BLK_ERR_CNTR(i),
      --
      BCLK     => MI_CLK,
      BRST     => '0',
      BDATAOUT => blk_err_cntr_r(i)
   );
end generate;

GEN_RXOK_CROSS: for i in PMA_RX_OK'range generate
   RX_OK_CROSS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map(
      ACLK     => '0',
      ARST     => '0',
      ADATAIN  => PMA_RX_OK(i),
      --
      BCLK     => MI_CLK,
      BRST     => '0',
      BDATAOUT => sync_pma_rx_ok(i)
   );
end generate;

GEN_SIGDET_CROSS: for i in PMD_SIG_DET'range generate
   RX_SIGDET_CROSS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map (
      ACLK     => '0',
      ARST     => '0',
      ADATAIN  => PMD_SIG_DET(i),
      --
      BCLK     => MI_CLK,
      BRST     => '0',
      BDATAOUT => sync_pmd_sig_det(i)
   );
end generate;

GEN_PMASTAT_CROSS: for i in PMA_STATUS'range generate
   PMASTAT_CROSS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map (
      ACLK     => '0',
      ARST     => '0',
      ADATAIN  => PMA_STATUS(i),
      --
      BCLK     => MI_CLK,
      BRST     => '0',
      BDATAOUT => pma_status_sync(i)
   );
end generate;

GEN_PCSSTAT_CROSS: for i in PCS_STATUS'range generate
   PCSSTAT_CROSS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map (
      ACLK     => '0',
      ARST     => '0',
      ADATAIN  => PCS_STATUS(i),
      --
      BCLK     => MI_CLK,
      BRST     => '0',
      BDATAOUT => sync_pcs_status(i)
   );
end generate;

GEN_PCSCTRL_CROSS: for i in PCS_CONTROL_I'range generate
   PCSCTRL_CROSS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map (
      ACLK     => '0',
      ARST     => '0',
      ADATAIN  => PCS_CONTROL_I(i),
      --
      BCLK     => MI_CLK,
      BRST     => '0',
      BDATAOUT => sync_pcs_control(i)
   );
end generate;

GEN_RSFEC_STATS: if (RSFEC_ABLE = '1') generate

GEN_FEC_AM_LOCK_CROSS: for i in FEC_AM_LOCK'range generate
   FEC_AM_LOCK_CROSS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map ( ADATAIN  => FEC_AM_LOCK(i), BCLK => MI_CLK, BDATAOUT => fec_am_lock_sync(i));
end generate;

FEC_HI_SER_CROSS: entity work.ASYNC_OPEN_LOOP
generic map(IN_REG  => false, TWO_REG => true)
port map ( ADATAIN  => FEC_HI_SER, BCLK => MI_CLK, BDATAOUT => FEC_HI_SER_sync);

FEC_ALGN_STAT_CROSS: entity work.ASYNC_OPEN_LOOP
generic map(IN_REG  => false, TWO_REG => true)
port map ( ADATAIN  => FEC_ALGN_STAT, BCLK => MI_CLK, BDATAOUT => FEC_ALGN_STAT_sync);

FEC_LANE_MAP_CROSS: for i in FEC_LANE_MAP'range generate
   FEC_LANE_MAP_CROSS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map ( ADATAIN  => FEC_LANE_MAP(i), BCLK => MI_CLK, BDATAOUT => FEC_LANE_MAP_sync(i));
end generate;

FEC_SYM_ERR_CROSS: for i in FEC_SYM_ERR'range generate
   FEC_CW_ERR_CROSS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map ( ADATAIN  => FEC_SYM_ERR(i), BCLK => MI_CLK, BDATAOUT => FEC_SYM_ERR_sync(i));
end generate;

FEC_COR_ERR_CROSS: for i in FEC_COR_ERR'range generate
   FEC_COR_ERR_CROSS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map ( ADATAIN  => FEC_COR_ERR(i), BCLK => MI_CLK, BDATAOUT => FEC_COR_ERR_sync(i));
end generate;

FEC_UNCOR_ERR_CROSS: for i in FEC_UNCOR_ERR'range generate
   FEC_UNCOR_ERR_CROSS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map ( ADATAIN  => FEC_UNCOR_ERR(i), BCLK => MI_CLK, BDATAOUT => FEC_UNCOR_ERR_sync(i));
end generate;

FEC_TX_BIP_CROSS: for i in FEC_TX_BIP'range generate
   FEC_TX_BIP_CROSS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map ( ADATAIN  => FEC_TX_BIP(i), BCLK => MI_CLK, BDATAOUT => FEC_TX_BIP_sync(i));
end generate;

FEC_TX_LANE_MAP_CROSS: for i in FEC_TX_LANE_MAP'range generate
   FEC_TX_LANE_MAP_CROSS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map ( ADATAIN  => FEC_TX_LANE_MAP(i), BCLK => MI_CLK, BDATAOUT => FEC_TX_LANE_MAP_sync(i));
end generate;

FEC_TX_BLK_LOCK_CROSS: for i in FEC_TX_BLK_LOCK'range generate
   FEC_TX_BLK_LOCK_CROSS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map ( ADATAIN  => FEC_TX_BLK_LOCK(i), BCLK => MI_CLK, BDATAOUT => FEC_TX_BLK_LOCK_sync(i));
end generate;

FEC_TX_ALGN_STAT_CROSS: for i in FEC_TX_ALGN_STAT'range generate
   FEC_TX_ALGN_STAT_CROSS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map ( ADATAIN  => FEC_TX_ALGN_STAT(i), BCLK => MI_CLK, BDATAOUT => FEC_TX_ALGN_STAT_sync(i));
end generate;

end generate; -- if RSFEC_ABLE

---------------------------------------------------

process(MI_CLK)
begin
   if rising_edge(MI_CLK) then
      if (drp_drdy_sync = '1') then
         drpdo_r <= drp_drd_sync;
      end if;
      -- DRP read ready/done flag
      if (drpen_i = '1') and (drpwe_r = '0') then
         drpbusy_r <= '1';
      elsif (drp_drdy_sync = '1') then
         drpbusy_r <= '0';
      end if;
   end if;
end process;

drpbusy <= (drpen_i and (not drpwe_r)) or drpbusy_r;

drp_cdc_i : entity work.MI_ASYNC
generic map (
   DATA_WIDTH => drpdo_r'high+1,
   ADDR_WIDTH => drpaddr_r'high+1,
   META_WIDTH => drpsel_r'high+1,
   RAM_TYPE   => "LUT",
   DEVICE     => DEVICE
)
port map (
   CLK_M     => MI_CLK,
   RESET_M   => RESET,
   MI_M_DWR  => drpdi_r ,
   MI_M_MWR  => drpsel_r ,
   MI_M_ADDR => drpaddr_r,
   MI_M_RD   => drpen_i and not drpwe_r,
   MI_M_WR   => drpen_i and drpwe_r,
   MI_M_BE   => (others => '1'),
   MI_M_DRD  => drp_drd_sync,
   MI_M_ARDY => open,
   MI_M_DRDY => drp_drdy_sync,

   CLK_S     => DRPCLK,
   RESET_S   => '0',
   MI_S_DWR  => DRPDI,
   MI_S_MWR  => DRPSEL,
   MI_S_ADDR => DRPADDR,
   MI_S_RD   => drp_rd,
   MI_S_WR   => drp_wr,
   MI_S_BE   => open,
   MI_S_DRD  => DRPDO,
   MI_S_ARDY => DRPARDY,
   MI_S_DRDY => DRPRDY
);

DRPWE <= drp_wr;
DRPEN <= drp_wr or drp_rd;

----

rx_sig_det(PMD_SIG_DET'high downto 0) <= sync_pmd_sig_det;
pma_rxl_stat <= AND_REDUCE(sync_pma_rx_ok);
rx_sig_det_g <= AND_REDUCE(sync_pmd_sig_det);
pma_fault    <= tx_fault or rx_fault;
tx_fault     <= '0';
rx_fault     <= (not pma_rxl_stat) or (not rx_sig_det_g);

UNUSED_FLAGS: if NUM_LANES < 20 generate
   rx_sig_det(rx_sig_det'high downto PMD_SIG_DET'high+1)            <= (others => '0');
   lane_map_i(lane_map_i'high downto sync_lane_map'high+1)          <= (others => '0');
   lane_align_i(lane_align_i'high downto sync_lane_align'high+1)    <= (others => '0');
   bip_ercntr_r(bip_ercntr_r'high downto sync_bip_err_cntrs'high+1) <= (others => '0');
   pcs_blk_lock(pcs_blk_lock'high downto sync_blk_lock'high+1)      <= (others => '0');
end generate;

lane_map_i(sync_lane_map'high downto 0)        <= sync_lane_map;
lane_align_i(sync_lane_align'high downto 0)    <= sync_lane_align;
pcs_blk_lock(sync_blk_lock'high downto 0)      <= sync_blk_lock;
bip_ercntr_r(sync_bip_err_cntrs'high downto 0) <= sync_bip_err_cntrs;
pcs_blk_lock_g <= AND_REDUCE(sync_blk_lock) and sync_algn_locked; -- ALGN_LOCKED should be included according to 802.2ba
pcs_fault      <= (not pcs_blk_lock_g) or (pcs_hi_ber) or (not pcs_rxl_stat);

mi_addr_masked <= MI_ADDR and X"0003FFFF";

ADDR_DECODE: process(all)
begin
   r333_rd  <= '0';
   r301_rd  <= '0';
   r308_rd  <= '0';
   r1201_rd <= '0';
   r1203_rd <= '0';
   r1205_rd <= '0';
   r1211_rd <= '0';
   r1213_rd <= '0';
   r1215_rd <= '0';
   r1217_rd <= '0';
   r3200_rd <= (others => '0');
   mi_drd_i <= (others => '0');
   ----------------------------------------------------------------------------
   -- PMA
   ----------------------------------------------------------------------------
   if mi_addr_masked(19 downto 15) = "00010" then -- select PMA (device 0x1)
      case mi_addr_masked(8 downto 2) is
          when "0000000" => -- PMA status1 & control 1        11    10:7      6:2          1             0
             mi_drd_i(15 downto  0) <= pma_rst & "010" & low_pwr & "0000" & "10000" & pma_rem_lpbk & pma_loc_lpbk; -- r1.0
             case speed_int is
                when 400 => mi_drd_i(5 downto  2)  <= "1001";
                when 200 => mi_drd_i(5 downto  2)  <= "1000";
                when 100 => mi_drd_i(5 downto  2)  <= "0011";
                when 50  => mi_drd_i(5 downto  2)  <= "0101";
                when 40  => mi_drd_i(5 downto  2)  <= "0010";
                when 25  => mi_drd_i(5 downto  2)  <= "0100";
                when others  => mi_drd_i(5 downto  2)  <= "0000"; -- 10G
             end case;
             mi_drd_i(31 downto 16) <= X"00" & pma_fault & "0000" & pma_rxl_stat & "10";                                      -- r1.1
          when "0000001" => -- PMA device identifier
             mi_drd_i(15 downto  0) <= X"18EC"; -- r1.2
             mi_drd_i(31 downto 16) <= X"0000"; -- r1.3
          when "0000010" => -- PMA devices in package 0 & speed ability
             mi_drd_i(15 downto  0) <= speed_cap_int;
             mi_drd_i(31 downto 16) <= "0000000000001010";  -- Devices in package (PMA & PCS) -- 0x000A -- r1.5
          when "0000011" => -- r1.6, r1.7: PMA  control 2 & devices in package (high word)
             mi_drd_i(15 downto 0)  <= X"0000"; -- Devices in package -- r1.6
             --
             mi_drd_i(16+15 downto 16+7) <= "000000000"; -- r1.7.15:7
             mi_drd_i(16+ 6 downto 16+0) <= pma_mode;     -- r1.7.6:0
          when "0000100" => -- PMA transmit disable & status 2 -- 0x...C
             mi_drd_i(15 downto 0)  <= "1011" & tx_fault & rx_fault & "0100000001"; -- Status 2 - r1.8
             if SPEED_CAP_10G = '1' then
                -- Add 10G abilities: -SR, -LR, -ER
                mi_drd_i(7 downto 5) <= "111";
             else
                -- Other speeds -> enable extended abilities in r1.11
                mi_drd_i(9) <= '1';
             end if;
             mi_drd_i(31 downto 16) <= "00000" & tx_dis & tx_dis_g; -- PMD transmit disable - r1.9
          when "0000101" => -- PMA/PMD extended ability registers & receive signal detect
             mi_drd_i(15 downto 0)  <= "00000" & rx_sig_det & rx_sig_det_g; -- Receive signal detect r1.10
             mi_drd_i(31 downto 16) <= "0000000000000000"; -- Extended ability register r1.11
             -- For 200/400G speeds enable extended abilities in r1.23 and r1.24
             if (SPEED_CAP_200G = '1' or SPEED_CAP_400G = '1') then
                mi_drd_i(16+13) <= '1';
             end if;
             -- For 40/100G speeds enable extended abilities in r1.13
             if (SPEED_CAP_100G = '1' or SPEED_CAP_40G = '1') then
                mi_drd_i(16+10) <= '1';
             end if;
             -- 25G: Enable extended capabilities in 1.19
             if (SPEED_CAP_25G = '1') then
                mi_drd_i(16+12) <= '1';
             end if;
          when "0000110" => -- 10G-EPON PMA/PMD P2MP ability register  & 40G/100G PMA/PMD extended ability register
             --- TBD:
             mi_drd_i(15 downto  0)  <= X"0000";  -- 10G-EPON PMA/PMD P2MP ability register r1.12
             mi_drd_i(31 downto 16)  <= X"0000";  -- 40G/100G PMA/PMD extended ability register r1.13
             mi_drd_i(16+6 downto 16) <= '0' & SPEED_CAP_40G & '0' & SPEED_CAP_40G & SPEED_CAP_40G & (SPEED_CAP_40G and AN_ABLE) & '0'; -- 40G/100G PMA/PMD extended ability register r1.13
             mi_drd_i(16+15) <= '1';                 -- PMA Remote loopback
             if (PMA_LANES = 10) then
                mi_drd_i(16+7)               <= '0'; -- 100GBASE-SR4
                mi_drd_i(16+9 downto 16+8)   <= SPEED_CAP_100G & SPEED_CAP_100G; -- 100GBASE-SR10 & 100GBASE-CR10
                mi_drd_i(16+11 downto 16+10) <= "00"; -- 100GBASE-ER4 & 100GBASE-LR4
                mi_drd_i(16+13 downto 16+12) <= "00"; -- 100GBASE-KR4 & 100GBASE-KP4
                mi_drd_i(16+14)              <= '0';  -- 100GBASE-CR4
             elsif (PMA_LANES = 4) then
                mi_drd_i(16+7)               <= (SPEED_CAP_100G and RSFEC_ABLE); -- 100GBASE-SR4
                mi_drd_i(16+9 downto 16+8)   <= "00"; -- 100GBASE-SR10 & 100GBASE-CR10
                mi_drd_i(16+11 downto 16+10) <= SPEED_CAP_100G & SPEED_CAP_100G; -- 100GBASE-ER4 & 100GBASE-LR4
                mi_drd_i(16+13 downto 16+12) <= "00"; -- 100GBASE-KR4 & 100GBASE-KP4
                mi_drd_i(16+14)              <= (SPEED_CAP_100G and RSFEC_ABLE); -- 100GBASE-CR4
             end if;
          when "0000111" => -- PMA/PMD package identifier
             mi_drd_i(15 downto 0)  <= X"0000"; -- r1.14
             mi_drd_i(31 downto 16) <= X"0000"; -- r1.15
          when "0001001" => -- r 1.18, r1.19 - PMA/PMD extended ability register
             mi_drd_i(15 downto 0)  <= X"0000"; -- r1.18
             mi_drd_i(31 downto 16) <= X"0000"; -- r1.19 -- PMA/PMD extended ability register
             mi_drd_i(16+7) <= SPEED_CAP_25G and RSFEC_ABLE; -- 25GBASE-ER
             mi_drd_i(16+6) <= SPEED_CAP_25G and RSFEC_ABLE; -- 25GBASE-LR
             mi_drd_i(16+5) <= '0';                          -- 25GBASE-T
             mi_drd_i(16+4) <= SPEED_CAP_25G and RSFEC_ABLE; -- 25GBASE-SR
             mi_drd_i(16+3) <= SPEED_CAP_25G and RSFEC_ABLE; -- 25GBASE-CR;  NOTE: "AN_ABLE" should be TRUE to be ieee compliant
             mi_drd_i(16+2) <= SPEED_CAP_25G;  -- 25GBASE-CR-S NOTE: Not IEEE compliant as CR medium should include AN
             mi_drd_i(16+1) <= '0';            -- 25GBASE-KR
             mi_drd_i(16+0) <= '0';            -- 25GBASE-KR-S
          when "0001010" => -- r 1.20, r1.21 - PMA/PMD extended ability register
             mi_drd_i(15 downto 0)  <= X"0000"; -- r1.20 -- 50G PMA/PMD extended ability register
             mi_drd_i(15) <= '1'; -- 50G PMA remote loopback ability
             mi_drd_i(5) <= SPEED_CAP_50G; -- 50GBASE-ER
             mi_drd_i(4) <= SPEED_CAP_50G; -- 50GBASE-LR
             mi_drd_i(3) <= SPEED_CAP_50G; -- 50GBASE-FR
             mi_drd_i(2) <= SPEED_CAP_50G; -- 50GBASE-SR
             mi_drd_i(1) <= SPEED_CAP_50G and AN_ABLE; -- 50GBASE-CR
             mi_drd_i(0) <= '0';           -- 50GBASE-KR
             mi_drd_i(31 downto 16) <= X"0000"; -- r1.21 -- 2.5G/5G PMA/PMD extended ability register
          when "0001011" => -- r 1.22, r1.23 - PMA/PMD extended ability register
             mi_drd_i(15 downto 0)  <= X"0000"; -- r1.22 -- BASE-H PMA/PMD extended ability register
             mi_drd_i(31 downto 16) <= X"0000"; -- r1.23 -- 200G PMA/PMD extended ability register
             mi_drd_i(16+15) <= '1'; -- 200G PMA remote loopback ability
             mi_drd_i(16+6) <= SPEED_CAP_200G; -- 200GBASE-ER4
             mi_drd_i(16+5) <= SPEED_CAP_200G; -- 200GBASE-LR4
             mi_drd_i(16+4) <= SPEED_CAP_200G; -- 200GBASE-FR4
             mi_drd_i(16+3) <= SPEED_CAP_200G; -- 200GBASE-DR4
             mi_drd_i(16+2) <= SPEED_CAP_200G; -- 200GBASE-SR4
             mi_drd_i(16+1) <= SPEED_CAP_200G and AN_ABLE; -- 200GBASE-CR4
             mi_drd_i(16+0) <= '0';            -- 200GBASE-KR4
          when "0001100" => -- r 1.24, r1.25 - PMA/PMD extended ability register
             mi_drd_i(15 downto 0)  <= X"0000"; -- r1.24 -- 400G PMA/PMD extended ability register
             mi_drd_i(15) <= '1'; -- 400G PMA remote loopback ability
             mi_drd_i(10) <= SPEED_CAP_400G; -- 400GBASE-ER8
             mi_drd_i(9)  <= SPEED_CAP_400G; -- 400GBASE-LR4-6
             mi_drd_i(8)  <= SPEED_CAP_400G; -- 400GBASE-FR4
             mi_drd_i(7)  <= SPEED_CAP_400G; -- 400GBASE-SR4-2
             mi_drd_i(6)  <= SPEED_CAP_400G; -- 400GBASE-SR8
             mi_drd_i(5)  <= SPEED_CAP_400G; -- 400GBASE-LR8
             mi_drd_i(4)  <= SPEED_CAP_400G; -- 400GBASE-FR8
             mi_drd_i(3)  <= SPEED_CAP_400G; -- 400GBASE-DR8
             mi_drd_i(2)  <= '0';            -- 400GBASE-SR16
             mi_drd_i(31 downto 16) <= X"0000"; -- r1.25 -- PMA/PMD extended ability 2 register
             mi_drd_i(16+0) <= SPEED_CAP_50G; -- enable 50G extended abilities (r1.20)
          when "0001101" => -- r 1.26, r1.27 - 40/100 PMA/PMD extended ability 2
             mi_drd_i(15 downto 0)  <= X"0000"; -- r1.26 -- 40/100G PMA/PMD extended ability register 2
             if PMA_LANES = 2 then
                 mi_drd_i(9)  <= SPEED_CAP_100G;             -- 100GBASE-SR2
                 mi_drd_i(8)  <= SPEED_CAP_100G and AN_ABLE; -- 100GBASE-CR2
                 mi_drd_i(7)  <= '0';                        -- 100GBASE-KR2
             elsif PMA_LANES = 1 then
                 mi_drd_i(6)  <= '0';            -- 100GBASE-ZR
                 mi_drd_i(5)  <= SPEED_CAP_100G; -- 100GBASE-LR1
                 mi_drd_i(4)  <= SPEED_CAP_100G; -- 100GBASE-FR1
                 mi_drd_i(3)  <= SPEED_CAP_100G; -- 100GBASE-DR
             end if;
             mi_drd_i(31 downto 16) <= X"0000"; -- r1.27 -- PMD transmitt disable extension

          -- RS-FEC ---------------------------------------------------------------------------
          when "1100100" => -- 0x190
             mi_drd_i(15 downto 0)  <= X"000" & "0" & fec_en_r & fec_ind_bypass_r & fec_cor_bypass_r; -- 1.200 RS-FEC control reg
             mi_drd_i(31 downto 16) <= fec_pcs_algn_stat & fec_algn_stat_sync & "00" & fec_am_lock_sync & "00000" & fec_hi_ser_sync & '1' & '1'; -- 1.201 RS-FEC status  reg
             r1201_rd <= MI_RD and (MI_BE(3) or MI_BE(2));
          when "1100101" => -- 0x194
             mi_drd_i(15 downto 0)  <= fec_cor_err_sync(15 downto  0); -- 1.202,203: RS-FEC corrected codewords counter
             mi_drd_i(31 downto 16) <= fec_cor_err_sync(31 downto 16);
             r1203_rd <= MI_RD and (MI_BE(3) or MI_BE(2));
          when "1100110" => -- 0x198
             mi_drd_i(15 downto 0)  <= fec_uncor_err_sync(15 downto  0); -- 1.204,205: RS-FEC uncorrected codewords counter
             mi_drd_i(31 downto 16) <= fec_uncor_err_sync(31 downto 16);
             r1205_rd <= MI_RD and (MI_BE(3) or MI_BE(2));
          when "1100111" => -- 0x19C
             mi_drd_i(15 downto 0)  <= X"00" & fec_lane_map_sync; -- 1.206: RS-FEC lane mapping register
             -- mi_drd_i(31 downto 16) <= X"0000"; -- Reserved
          when "1101001" => -- 0x1A4
             mi_drd_i(15 downto 0)  <= fec_sym_err_sync(1*16-1 downto 0*16); -- 1.210 RS-FEC symbol error counter, lane 0
             mi_drd_i(31 downto 16) <= fec_sym_err_sync(2*16-1 downto 1*16); -- 1.211 RS-FEC symbol error counter, lane 0
             r1211_rd <= MI_RD and (MI_BE(3) or MI_BE(2));
          when "1101010" => -- 0x1A8
             mi_drd_i(15 downto 0)  <= fec_sym_err_sync(3*16-1 downto 2*16); -- 1.212 RS-FEC symbol error counter, lane 1
             mi_drd_i(31 downto 16) <= fec_sym_err_sync(4*16-1 downto 3*16); -- 1.213 RS-FEC symbol error counter, lane 1
             r1213_rd <= MI_RD and (MI_BE(3) or MI_BE(2));
          when "1101011" => -- 0x1AC
             mi_drd_i(15 downto 0)  <= fec_sym_err_sync(5*16-1 downto 4*16); -- 1.214 RS-FEC symbol error counter, lane 2
             mi_drd_i(31 downto 16) <= fec_sym_err_sync(6*16-1 downto 5*16); -- 1.215 RS-FEC symbol error counter, lane 2
             r1215_rd <= MI_RD and (MI_BE(3) or MI_BE(2));
          when "1101100" => -- 0x1B0
             mi_drd_i(15 downto 0)  <= fec_sym_err_sync(7*16-1 downto 6*16); -- 1.214 RS-FEC symbol error counter, lane 3
             mi_drd_i(31 downto 16) <= fec_sym_err_sync(8*16-1 downto 7*16); -- 1.215 RS-FEC symbol error counter, lane 3
             r1217_rd <= MI_RD and (MI_BE(3) or MI_BE(2));
          -- TODO:
             -- 1.230-249: RS-FEC BIP error counter, lane 0 to 19  -- Allways zero for integrated RS-FEC
             -- 1.250-269: RS-FEC PCS lane mapping, lane 0 to 19   -- 0...20 for integrated RS-FEC
             -- 1.280-283: RS-FEC PCS alignment status 1 through 4 -- All locked for integrated RS-FEC
             --                signal FEC_TX_BIP_sync
             --                signal FEC_TX_LANE_MAP_sync
             --                signal FEC_TX_BLK_LOCK_sync
             --                signal FEC_TX_ALGN_STAT_sync
          when others =>
                mi_drd_i <= (others => '0');


          -- TODO:
          -- 1.1500    Test pattern ability 45.2.1.95
          -- 1.1501    PRBS pattern testing control 45.2.1.96
          -- 1.1510    Square wave testing control 45.2.1.97
          -- 1.1600 - 1609 PRBS Tx error counters, lane 0 through lane 9 45.2.1.98
          -- 1.1700 - 1709 PRBS Rx error counters, lane 0 through lane 9 45.2.1.99
         end case;


   elsif mi_addr_masked(19 downto 15) = "00011" then -- select PMA vendor specific registers
      case mi_addr_masked(5 downto 2) is
         when "0000" => -- 0x8000 - vendor specific PMA control register
            mi_drd_i <= pma_control_r;
         when "0001" =>  -- 0x8004
            mi_drd_i(pma_status_sync'range) <= pma_status_sync;
         when "0010" =>  -- 0x8008
            mi_drd_i(1 downto 0) <= fec_tx_en_r & fec_rx_en_r;  -- 0x8008
         -- DRP control registers
         when "0100" => -- 0x8010: DRP data
            mi_drd_i(drpdo_r'range) <= drpdo_r;
         when "0101" => -- 0x8014: DRP address
            mi_drd_i(drpaddr_r'range) <= drpaddr_r;
         when "0110" => -- 0x8018: DRP control
            mi_drd_i(31) <= drpbusy;
         when "1000" => -- 0x8020
            mi_drd_i <= pma_drive_r;
         when "1001" => -- 0x8024
            mi_drd_i <= pma_precursor_r;
         when "1010" => -- 0x8028
            mi_drd_i <= pma_postcursor_r;
         when others =>
      end case;
   end if;
   -------------------------------------------------------------------------
   --- PCS registers -------------------------------------------------------
   -------------------------------------------------------------------------
   if mi_addr_masked(19 downto 16) = X"3" then -- select PCS (device 0x3)
      if mi_addr_masked(15)  = '1' then
         case mi_addr_masked(3 downto 2) is
            when "00" =>
               mi_drd_i(15 downto  0) <= sync_pcs_control(15 downto 0);
               mi_drd_i(31 downto 16) <= sync_pcs_status(15 downto 0);
            when others => mi_drd_i <= (others => '0');
         end case;
      elsif mi_addr_masked(9 downto 7) = "000" then
         case mi_addr_masked(6 downto 2) is
            when "00000" => -- 0x0000
               mi_drd_i(15 downto  0) <= pcs_rst & pcs_lpbk & "10" & pcs_low_pwr & "00001" & "0000" & scr_bypass_r;-- 3.0 PCS control 1 -- r3.0
               case speed_int is
                  when 400 =>    mi_drd_i( 5 downto  2) <= "1010"; -- 400G
                  when 200 =>    mi_drd_i( 5 downto  2) <= "1001"; -- 200G
                  when 100 =>    mi_drd_i( 5 downto  2) <= "0100"; -- 100G
                  when  50 =>    mi_drd_i( 5 downto  2) <= "0110"; -- 50G
                  when  40 =>    mi_drd_i( 5 downto  2) <= "0011"; -- 40G
                  when  25 =>    mi_drd_i( 5 downto  2) <= "0101"; -- 25G
                  when others => mi_drd_i( 5 downto  2) <= "0000"; -- 10G
               end case;
               mi_drd_i(31 downto 16) <= X"00" & pcs_fault & "0000" & pcs_rxl_stat_l & "00"; -- 3.1 PCS status 1 -- r3.1
               r301_rd <= MI_RD and (MI_BE(3) or MI_BE(2));
            when "00001" => -- 0x0004
               mi_drd_i(15 downto  0) <= X"18EC"; -- 3.2 PCS device identifier  -- r3.2
               mi_drd_i(31 downto 16) <= X"0000"; -- 3.3 PCS device identifier  -- r3.3
            when "00010" => -- 0x0008
               mi_drd_i(15 downto  0) <= X"0000"; -- 3.4 PCS speed ability      -- r3.4
               mi_drd_i(0) <= SPEED_CAP_10G;      -- 3.4.0 10G
               mi_drd_i(2) <= SPEED_CAP_40G;      -- 3.4.2 40G
               mi_drd_i(3) <= SPEED_CAP_100G;     -- 3.4.3 100G
               mi_drd_i(4) <= SPEED_CAP_25G;      -- 3.4.4 25G
               mi_drd_i(5) <= SPEED_CAP_50G;      -- 3.4.5 50G
               mi_drd_i(8) <= SPEED_CAP_200G;     -- 3.4.8 200G
               mi_drd_i(9) <= SPEED_CAP_400G;     -- 3.4.9 400G
               mi_drd_i(31 downto 16) <= X"0000"; -- 3.5 PCS devices in package -- r3.5
            when "00011" => -- 0x000C
               mi_drd_i(15 downto  0) <= X"0007"; -- 3.6 PCS devices in package -- r3.6
               mi_drd_i(31 downto 16) <= X"0000"; -- 3.7 10G PCS control 2      -- r3.7
               case speed_int is
                  when 400 =>    mi_drd_i(16+3 downto  16+0) <= "1101"; -- 400G
                  when 200 =>    mi_drd_i(16+3 downto  16+0) <= "1100"; -- 200G
                  when 100 =>    mi_drd_i(16+3 downto  16+0) <= "0101"; -- 100G
                  when  50 =>    mi_drd_i(16+3 downto  16+0) <= "1000"; -- 50G
                  when  40 =>    mi_drd_i(16+3 downto  16+0) <= "0100"; -- 40G
                  when  25 =>    mi_drd_i(16+3 downto  16+0) <= "0111"; -- 25G
                  when others => mi_drd_i(16+3 downto  16+0) <= "0000"; -- 10G
               end case;
            when "00100" => -- 0x0010
               mi_drd_i(15 downto  0) <= "1000" & '0' & pcs_fault_l & "0" & SPEED_CAP_50G & SPEED_CAP_25G & '0' & SPEED_CAP_100G & SPEED_CAP_40G & "000" & SPEED_CAP_10G; -- r3.8 10G PCS status 2
               mi_drd_i(31 downto 16) <= X"0000"; -- 3.9 rsvd
               mi_drd_i(16+1 downto 16+0) <= SPEED_CAP_400G & SPEED_CAP_200G;
               r308_rd <= MI_RD and (MI_BE(1) or MI_BE(0));
            when "00111" =>  -- 0x001C
               mi_drd_i(15 downto  0) <= X"0000"; -- 3.14 PCS package identifier
               mi_drd_i(31 downto 16) <= X"0000"; -- 3.15 PCS package identifier
            when "01100" => -- 0x0030: 3.24 - 10GBASE-X PCS status & test control
               mi_drd_i(15 downto  0) <= X"0000";
               mi_drd_i(31 downto 16) <= X"0000";
            when "10000" => -- 0x0040: 3.32, 3.33 GBASE-R and GBASE-T PCS status 1 & 2 -- 0x...40
               mi_drd_i(15 downto  0) <= "000" & pcs_rxl_stat & X"00" & "00" & pcs_hi_ber & pcs_blk_lock_g; -- 3.32  GBASE-R and GBASE-T PCS status 1
               mi_drd_i(31 downto 16) <= pcs_blk_lock_l & pcs_hi_ber_l & ber_count_r(5 downto 0) & blk_err_cntr_r(7 downto 0); -- 3.33  10GBASE-R and 10GBASE-T PCS status 2
               r333_rd <= MI_RD and (MI_BE(3) or MI_BE(2));
            when "10001" => -- 3.34, 10GBASE-R PCS test pattern seed A -- 0x...44
               mi_drd_i(15 downto  0) <= X"0000";
               mi_drd_i(31 downto 16) <= X"0000";
            when "10010" => -- 3.36, 10GBASE-R PCS test pattern seed A -- 0x...48
               mi_drd_i(15 downto  0) <= X"0000";
               mi_drd_i(31 downto 16) <= X"0000";
            when "10011" => -- 3.38, 10GBASE-R PCS test pattern seed B -- 0x...4C
               mi_drd_i(15 downto  0) <= X"0000";
               mi_drd_i(31 downto 16) <= X"0000";
            when "10100" => -- 3.40, 10GBASE-R PCS test pattern seed B -- 0x...50
               mi_drd_i(15 downto  0) <= X"0000";
               mi_drd_i(31 downto 16) <= X"0000";
            when "10101" => -- 0x...54
               mi_drd_i(15 downto  0) <= X"0000"; -- 3.42  10GBASE-R PCS test pattern control
               mi_drd_i(31 downto 16) <= X"0000"; -- 3.43  10GBASE-R PCS test pattern error counter
            when "10110" => -- 0x...58
               mi_drd_i(15 downto  0) <= ber_count_l; -- 3.44  BER high order counter(21:6)
               mi_drd_i(31 downto 16) <= "10" & blk_err_cntr_l; -- 3.45  Errored blocks high order counter
            when "11001" => -- 3.50, 3.51 Multi-lane BASE-R PCS block lock status 1 through 4 -- 0x...64
               mi_drd_i(15 downto  0) <= "000" & pcs_blk_lock_g & X"0" & pcs_blk_lock(7 downto 0);
               mi_drd_i(31 downto 16) <= X"0" & pcs_blk_lock(19 downto 8);
            when "11010" => -- 3.52, 3.53 Multi-lane BASE-R PCS alignment status 1 through 4 -- 0x...68
               mi_drd_i(15 downto  0) <= X"00" & lane_align_i(7 downto 0); -- aligned flags for each lane
               mi_drd_i(31 downto 16) <= X"0" & lane_align_i(19 downto 8); -- aligned flags for each lane
            when others =>
               mi_drd_i <= (others => '0');
         end case;
      elsif mi_addr_masked(9 downto 7) = "011" then -- xxx200 -- 0x...190
         case mi_addr_masked(5 downto 2) is
            -- BIP error counters, lanes 0 through 19
            when "0100" =>
               mi_drd_i(15 downto  0) <= bip_ercntr_r(1*16-1 downto 0*16); -- 3.200 BIP error counters, lane 0
               mi_drd_i(31 downto 16) <= bip_ercntr_r(2*16-1 downto 1*16); -- 3.201 BIP error counters, lane 1
               r3200_rd(0) <= MI_RD and (MI_BE(0) or MI_BE(1));
               r3200_rd(1) <= MI_RD and (MI_BE(2) or MI_BE(3));
            when "0101" =>
               mi_drd_i(15 downto  0) <= bip_ercntr_r(3*16-1 downto 2*16); -- 3.202 BIP error counters, lane 2
               mi_drd_i(31 downto 16) <= bip_ercntr_r(4*16-1 downto 3*16); -- 3.203 BIP error counters, lane 3
               r3200_rd(2) <= MI_RD and (MI_BE(0) or MI_BE(1));
               r3200_rd(3) <= MI_RD and (MI_BE(2) or MI_BE(3));
            when "0110" =>
               mi_drd_i(15 downto  0) <= bip_ercntr_r(5*16-1 downto 4*16); -- 3.204 BIP error counters, lane 4
               mi_drd_i(31 downto 16) <= bip_ercntr_r(6*16-1 downto 5*16); -- 3.205 BIP error counters, lane 5
               r3200_rd(4) <= MI_RD and (MI_BE(0) or MI_BE(1));
               r3200_rd(5) <= MI_RD and (MI_BE(2) or MI_BE(3));
            when "0111" =>
               mi_drd_i(15 downto  0) <= bip_ercntr_r(7*16-1 downto 6*16); -- 3.206 BIP error counters, lane 6
               mi_drd_i(31 downto 16) <= bip_ercntr_r(8*16-1 downto 7*16); -- 3.207 BIP error counters, lane 7
               r3200_rd(6) <= MI_RD and (MI_BE(0) or MI_BE(1));
               r3200_rd(7) <= MI_RD and (MI_BE(2) or MI_BE(3));
            when "1000" =>
               mi_drd_i(15 downto  0) <= bip_ercntr_r(9*16-1  downto 8*16); -- 3.208 BIP error counters, lane 8
               mi_drd_i(31 downto 16) <= bip_ercntr_r(10*16-1 downto 9*16); -- 3.209 BIP error counters, lane 9
               r3200_rd(8) <= MI_RD and (MI_BE(0) or MI_BE(1));
               r3200_rd(9) <= MI_RD and (MI_BE(2) or MI_BE(3));
            when "1001" =>
               mi_drd_i(15 downto  0) <= bip_ercntr_r(11*16-1 downto 10*16); -- 3.210 BIP error counters, lane 10
               mi_drd_i(31 downto 16) <= bip_ercntr_r(12*16-1 downto 11*16); -- 3.211 BIP error counters, lane 11
               r3200_rd(10) <= MI_RD and (MI_BE(0) or MI_BE(1));
               r3200_rd(11) <= MI_RD and (MI_BE(2) or MI_BE(3));
            when "1010" =>
               mi_drd_i(15 downto  0) <= bip_ercntr_r(13*16-1 downto 12*16); -- 3.212 BIP error counters, lane 12
               mi_drd_i(31 downto 16) <= bip_ercntr_r(14*16-1 downto 13*16); -- 3.213 BIP error counters, lane 13
               r3200_rd(12) <= MI_RD and (MI_BE(0) or MI_BE(1));
               r3200_rd(13) <= MI_RD and (MI_BE(2) or MI_BE(3));
            when "1011" =>
               mi_drd_i(15 downto  0) <= bip_ercntr_r(15*16-1 downto 14*16); -- 3.214 BIP error counters, lane 14
               mi_drd_i(31 downto 16) <= bip_ercntr_r(16*16-1 downto 15*16); -- 3.215 BIP error counters, lane 15
               r3200_rd(14) <= MI_RD and (MI_BE(0) or MI_BE(1));
               r3200_rd(15) <= MI_RD and (MI_BE(2) or MI_BE(3));
            when "1100" =>
               mi_drd_i(15 downto  0) <= bip_ercntr_r(17*16-1 downto 16*16); -- 3.216 BIP error counters, lane 16
               mi_drd_i(31 downto 16) <= bip_ercntr_r(18*16-1 downto 17*16); -- 3.217 BIP error counters, lane 17
               r3200_rd(16) <= MI_RD and (MI_BE(0) or MI_BE(1));
               r3200_rd(17) <= MI_RD and (MI_BE(2) or MI_BE(3));
            when "1101" =>
               mi_drd_i(15 downto  0) <= bip_ercntr_r(19*16-1 downto 18*16); -- 3.218 BIP error counters, lane 18
               mi_drd_i(31 downto 16) <= bip_ercntr_r(20*16-1 downto 19*16); -- 3.219 BIP error counters, lane 19
               r3200_rd(18) <= MI_RD and (MI_BE(0) or MI_BE(1));
               r3200_rd(19) <= MI_RD and (MI_BE(2) or MI_BE(3));
            when others =>
               mi_drd_i <= (others => '0');
         end case;
      elsif mi_addr_masked(9 downto 7) = "110" then  -- 0x...320
         case mi_addr_masked(6 downto 2) is
            when "01000" => -- 3.400 PCS lane mapping registers, lanes 0 through 19
               mi_drd_i(15 downto  0) <= "00000000000" & lane_map_i(1*5-1 downto 0*5);
               mi_drd_i(31 downto 16) <= "00000000000" & lane_map_i(2*5-1 downto 1*5);
            when "01001" => -- 3.402 PCS lane mapping registers, lanes 0 through 19
               mi_drd_i(15 downto  0) <= "00000000000" & lane_map_i(3*5-1 downto 2*5);
               mi_drd_i(31 downto 16) <= "00000000000" & lane_map_i(4*5-1 downto 3*5);
            when "01010" => -- 3.404 PCS lane mapping registers, lanes 0 through 19
               mi_drd_i(15 downto  0) <= "00000000000" & lane_map_i(5*5-1 downto 4*5);
               mi_drd_i(31 downto 16) <= "00000000000" & lane_map_i(6*5-1 downto 5*5);
            when "01011" => -- 3.406 PCS lane mapping registers, lanes 0 through 19
               mi_drd_i(15 downto  0) <= "00000000000" & lane_map_i(7*5-1 downto 6*5);
               mi_drd_i(31 downto 16) <= "00000000000" & lane_map_i(8*5-1 downto 7*5);
            when "01100" => -- 3.408 PCS lane mapping registers, lanes 0 through 19
               mi_drd_i(15 downto  0) <= "00000000000" & lane_map_i(9*5-1 downto 8*5);
               mi_drd_i(31 downto 16) <= "00000000000" & lane_map_i(10*5-1 downto 9*5);
            when "01101" => -- 3.410 PCS lane mapping registers, lanes 0 through 19
               mi_drd_i(15 downto  0) <= "00000000000" & lane_map_i(11*5-1 downto 10*5);
               mi_drd_i(31 downto 16) <= "00000000000" & lane_map_i(12*5-1 downto 11*5);
            when "01110" => -- 3.412 PCS lane mapping registers, lanes 0 through 19
               mi_drd_i(15 downto  0) <= "00000000000" & lane_map_i(13*5-1 downto 12*5);
               mi_drd_i(31 downto 16) <= "00000000000" & lane_map_i(14*5-1 downto 13*5);
            when "01111" => -- 3.414 PCS lane mapping registers, lanes 0 through 19
               mi_drd_i(15 downto  0) <= "00000000000" & lane_map_i(15*5-1 downto 14*5);
               mi_drd_i(31 downto 16) <= "00000000000" & lane_map_i(16*5-1 downto 15*5);
            when "10000" => -- 3.416 PCS lane mapping registers, lanes 0 through 19
               mi_drd_i(15 downto  0) <= "00000000000" & lane_map_i(17*5-1 downto 16*5);
               mi_drd_i(31 downto 16) <= "00000000000" & lane_map_i(18*5-1 downto 17*5);
            when "10001" => -- 3.418 PCS lane mapping registers, lanes 0 through 19
               mi_drd_i(15 downto  0) <= "00000000000" & lane_map_i(19*5-1 downto 18*5);
               mi_drd_i(31 downto 16) <= "00000000000" & lane_map_i(20*5-1 downto 19*5);
            when others =>
               mi_drd_i <= (others => '0');
         end case;
      end if;
   end if;
end process;

-- -------------------------------------------------------------------------------------
-- PMA mode settings --------------------------------------------------------------------
-- -------------------------------------------------------------------------------------
-- Set PMA mode (by writing reg 1.7) according to supported features
-- When the requsted mode is not supported, the current mode is preserved
set_pma_mode_p: process(all)
begin
   case speed_int is

      when 400 =>
         -- For 400GE, only the  400GBASE-SR8 -FR8 and -LR8 are supported
         pma_mode_set <= pma_mode;  -- Unsupported PMA mode - do not change
         if pm_req_hi(3 downto 0) = "1100" then --
             pma_mode_set(6 downto 2) <= "11000";
             pma_mode_set(1 downto 0) <= pm_req(1 downto 0);
         elsif pm_req_hi(3 downto 0) = "1011" then --
            pma_mode_set(6 downto 3) <= "1011";
            if pm_req = "111" or pm_req = "011" or pm_req = "100" or pm_req = "010" then
               pma_mode_set(2 downto 0) <= pm_req; -- 400GBASE-SR8 or -FR8 -DR4
            end if;
         end if;

      when 200 =>
         -- For 200GE, only the 200GBASE-CR4, -SR4, -DR4, -FR4 and -LR4 are supported
         pma_mode_set <= pma_mode;  -- Do not change the PMA mode by default
         if pm_req_hi(3 downto 0) = "1010" then
            if pm_req = "001" and AN_ABLE = '1' then
               pma_mode_set(6 downto 3) <= "1010";
               pma_mode_set(2 downto 0) <= pm_req; -- 200GBASE-CR4
            elsif pm_req = "010" or pm_req = "011" or pm_req = "100" or pm_req = "101" then
               pma_mode_set(6 downto 3) <= "1010";
               pma_mode_set(2 downto 0) <= pm_req; -- 200GBASE-SR4, -DR4, -FR4, -LR4
            end if;
         elsif pm_req_hi(3 downto 0) = "1011" then
            if pm_req = "000" then
               pma_mode_set(6 downto 3) <= "1011";
               pma_mode_set(2 downto 0) <= pm_req; -- 200GBASE-ER4
            end if;
         end if;

      when 100 =>
         pma_mode_set <= pma_mode;  -- Do not change the PMA mode by default
         if (PMA_LANES = 10) and pm_req_hi(3 downto 0) = "0101" then
            pma_mode_set(6 downto 1) <= "010100";
            pma_mode_set(         0) <= pm_req(0) or (not AN_ABLE); -- 0 = CR10 -> AN must be supported; 1 = SR10 -> always supported
         elsif (PMA_LANES = 2) and pm_req_hi(3 downto 0) = "1001" then
            pma_mode_set(6 downto 2) <= "10010";
            pma_mode_set(1 downto 0) <= pma_mode(1 downto 0);  -- Do not change the PMA mode by default
            if pm_req(1 downto 0) = "01" and AN_ABLE = '1' then -- -CR2 mode requested
               pma_mode_set(1 downto 0)  <= "01";  -- 100GBASE-CR2, supported only with AN
            elsif pm_req(1 downto 0) = "10" then
               pma_mode_set(1 downto 0)  <= "10";  -- 100GBASE-SR2
            end if;
         elsif (PMA_LANES = 1) and pm_req_hi(3 downto 0) = "1001" then
            pma_mode_set(6 downto 3) <= "1001";
            pma_mode_set(2 downto 0) <= pma_mode(2 downto 0);  -- Do not change the PMA mode by default
            if pm_req = "101" or pm_req = "100" or pm_req = "011" then
               pma_mode_set(2 downto 0) <= pm_req; -- 100GBASE-LR1 pr 100GBASE-FR1
            end if;
         elsif (PMA_LANES = 4) and pm_req_hi(3 downto 0) = "0101" then -- PMA_LANES = 4 -> -- 100GBASE-xR4
            pma_mode_set(6 downto 3) <= "0101";
            pma_mode_set(2 downto 0) <= pma_mode(2 downto 0);  -- Do not change the PMA mode by default
            if pm_req(2) = '1' then -- 100GBASE modes with RS-FEC
               if RSFEC_ABLE = '1' and fec_en_r = '1' then
                  pma_mode_set(2 downto 0) <= pm_req;
               end if;
            elsif pm_req(1) = '1' then
               pma_mode_set(2 downto 0) <= pm_req;
            end if;
         end if;

      when  50 =>
         pma_mode_set <= pma_mode;  -- Do not change the PMA mode by default
         if pm_req_hi(3 downto 0) = "1000" then
            if pm_req = "101" or pm_req = "010" or pm_req = "011" or pm_req = "100" then
               pma_mode_set(2 downto 0) <= pm_req; -- 50GBASE-ER, -LR, -FR, -SR,
            elsif pm_req = "001" and AN_ABLE = '1' then
               pma_mode_set(2 downto 0) <= pm_req; -- 50GBASE-CR
            end if;
         end if;

      when  40 =>
         pma_mode_set <= pma_mode;  -- Do not change the PMA mode by default
         if pm_req_hi(3 downto 0) = "0100" then
            if pm_req = "010" or pm_req = "011" then
               pma_mode_set(2 downto 0) <= pm_req;
            end if;
         end if;

      when  25 =>
         pma_mode_set <= pma_mode;  -- Do not change the PMA mode by default
         if pm_req_hi(3 downto 1) = "011" then
            if pm_req_hi(0) = '1' then
               if pm_req = "010" and RSFEC_ABLE = '1' then
                  pma_mode_set(3 downto 0) <= "1010"; -- 25GBASE-SR (warning: not compliant, AN should be also supported)
               elsif pm_req = "000" then
                  pma_mode_set(3 downto 0) <= "1000"; -- 25GBASE-CR-S (warning: not compliant, AN should be also supported)
               end if;
            else
               if (pm_req = "110" or pm_req = "101") and (RSFEC_ABLE = '1') then
                  pma_mode_set(3 downto 0) <= '0' & pm_req; -- 25GBASE-LR or 25GBASE-ER
               end if;
            end if;
         end if;

      when  others => -- 10
         pma_mode_set <= pma_mode;  -- Do not change the PMA mode by default
         if pm_req_hi = "0000" then
            if pm_req = "111" or pm_req = "110" or pm_req = "101" then
                pma_mode_set(2 downto 0) <= pm_req; -- 10GBASE-LR or 10GBASE-SR 10GBASE-ER
            end if;
         end if;
      end case;
   end process;

-- -------------------------------------------------------------------------------------
-- -------------------------------------------------------------------------------------

MI_READ_REGS: process(MI_CLK)
begin
   if MI_CLK'event and MI_CLK = '1' then
      MI_DRD    <= mi_drd_i;
      MI_DRDY   <= MI_RD;
      --
      r301_rd_r  <= r301_rd;
      r308_rd_r  <= r308_rd;
      r333_rd_r  <= r333_rd;
      r1201_rd_r <= r1201_rd;
      r1203_rd_r <= r1203_rd;
      r1205_rd_r <= r1205_rd;
      r1211_rd_r <= r1211_rd;
      r1213_rd_r <= r1213_rd;
      r1215_rd_r <= r1215_rd;
      r1217_rd_r <= r1217_rd;

      for i in 0 to 19 loop
         r3200_rd_r(i) <= r3200_rd(i);
      end loop;

   end if;
end process;

MI_ARDY <= MI_RD or MI_WR;

MI_WRITE: process(MI_CLK)
begin
   if MI_CLK'event and MI_CLK = '1' then
      PMA_RETUNE <= '0';
      drpen_i    <= '0';
      drpwe_r    <= '0';
      if async_rst_mi = '1' then
         case speed_int is -- default PMA modes
            when 400 => -- 400GBASE-SR8 TBD: -CR8 mode would be better, however it is not defined in ieee yet
               pma_mode <= "1011111";
            when 200 => -- 200GBASE-SR4
               pma_mode <= "1010010";
            when  50 => -- 50GBASE-SR
               pma_mode <= "1000010";
            when  100 => -- 100GBASE
               if PMA_LANES = 10 then
                   pma_mode <= "0101001"; -- 100GBASE-SR10
               elsif PMA_LANES = 4 then
                   if RSFEC_ABLE = '1' and RSFEC_EN_INIT = '1' then
                       pma_mode <= "0101111"; -- 100GBASE-SR4 (RSFEC on)
                   else
                       pma_mode <= "0101010"; -- 100GBASE-LR4
                   end if;
               elsif PMA_LANES = 2 then
                  pma_mode <= "1001010"; -- 100GBASE-SR2
               else
                  pma_mode <= "1001011"; -- 100GBASE-DR
               end if;
            when  40 => -- 40GBASE-SR4
               pma_mode <= "0100010";
            when  25 =>
               pma_mode <= "0111000"; -- 25GBASE-CR
            when  others => -- 10GBASE-LR
               pma_mode <= "0000110";
         end case;
         scr_bypass_r <= "00";
         pcs_lpbk     <= '0';
         pcs_rst      <= '0';
         pma_loc_lpbk <= '0';
         pma_rem_lpbk <= '0';
         pma_rst      <= '0';
         low_pwr      <= '0';
         tx_dis_g     <= '0';
         fec_tx_en_r  <= '1';
         fec_rx_en_r  <= '1';
         tx_dis       <= (others => '0');
         pma_control_r<= PMA_CONTROL_INIT;
         pma_precursor_r  <= PMA_PRECURSOR_INIT;
         pma_postcursor_r <= PMA_POSTCURSOR_INIT;
         pma_drive_r      <= PMA_DRIVE_INIT;
      else
      --- PMA registers -------------------------------------------------------
      if (mi_addr_masked(19 downto 16) = X"1") and (MI_WR = '1') then -- select PMA (device 0x1)
         -- 0x8000 : Vendor specific control registers
         if mi_addr_masked(15) = '1' then
            case mi_addr_masked(5 downto 2) is
               when "0001" => -- 0x8004 - vendor specific PMA control register
                  pma_control_r <= MI_DWR(PMA_CONTROL'range);
                  PMA_RETUNE    <= MI_DWR(31);
               when "0010" =>  -- FEC enable register
                  fec_rx_en_r <=  MI_DWR(0);
                  fec_tx_en_r <=  MI_DWR(1);
               -- DRP control registers
               when "0100" => -- 0x8010: DRP data
                  drpdi_r <= MI_DWR(drpdi_r'range);
               when "0101" => -- 0x8014: DRP address
                  drpaddr_r <= MI_DWR(drpaddr_r'range);
               when "0110" => -- 0x8018:  DRP select, operation type (R/W) and start
                  drpen_i  <= '1';
                  drpsel_r <= MI_DWR(drpsel_r'high+4 downto 4);
                  drpwe_r  <= MI_DWR(0);
               when "1000" => -- 0x8020
                  pma_drive_r      <= MI_DWR;
               when "1001" => -- 0x8024
                  pma_precursor_r  <= MI_DWR;
               when "1010" => -- 0x8028
                  pma_postcursor_r <= MI_DWR;
               when others => null;
            end case;
         -- 0x0000 : IEEE standard PMA registers
         elsif mi_addr_masked(9 downto 7) = "000" then
            case mi_addr_masked(6 downto 2) is -- 1.0 PMA control 1
               when "00000" => -- PMA control
                  if (MI_BE(0) = '1') then
                     pma_loc_lpbk  <= MI_DWR(0);
                     pma_rem_lpbk  <= MI_DWR(1);
                     low_pwr       <= MI_DWR(11);
                     -- PMA_PTRN_EN   <= MI_DWR(13); -- Pattern generator enable - for debugg only
                     pma_rst       <= MI_DWR(15);
                  end if;
               when "00011" => -- r1.7: PMA  control 2 & devices in package (high word)
                  if (MI_BE(2) = '1') then
                     pma_mode  <= pma_mode_set;
                     fec_en_r  <= MI_DWR(18);
                  end if;
               when "00100" => -- PMA transmit disable
                  if (MI_BE(2) = '1') then
                     tx_dis_g <= MI_DWR(16);
                     tx_dis   <= MI_DWR(26 downto 17);
                  end if;
               when others => null;
            end case;
         elsif mi_addr_masked(9 downto 7) = "011" then -- FEC controls
            if mi_addr_masked(6 downto 2) = "00100" then -- 0x190, 1.200 RS-FEC control reg
               if (MI_BE(0) = '1') then
                  fec_cor_bypass_r <= MI_DWR(0);
                  fec_ind_bypass_r <= MI_DWR(1);
                  -- 25G RS-FEC enable
                  fec_en_r         <= MI_DWR(2);
               end if;
            end if;
         end if;
      --- PCS registers -------------------------------------------------------
      elsif (mi_addr_masked(19 downto 16) = X"3") and (MI_WR = '1') then -- select PCS (device 0x3)
         -- 0x8000 : Vendor specific control registers
         if mi_addr_masked(15) = '1' then
            case mi_addr_masked(3 downto 2) is
               when "00" =>
                  if (MI_BE(0) = '1') then
                      PCS_CONTROL(15 downto 0) <= MI_DWR(15 downto 0);
                  end if;
               when others => null;
            end case;
         elsif mi_addr_masked(9 downto 7) = "000" then
            case mi_addr_masked(6 downto 2) is -- 3.0 -- 3.0 PCS control 1
               when "00000" =>
                  if (MI_BE(0) = '1') then
                     scr_bypass_r <= MI_DWR(1 downto 0);
                     pcs_lpbk     <= MI_DWR(14);
                     pcs_rst      <= MI_DWR(15);
                  end if;
               when "10001" => -- 3.34, 10GBASE-R PCS test pattern seed A
               when "10010" => -- 3.36, 10GBASE-R PCS test pattern seed A
               when "10011" => -- 3.38, 10GBASE-R PCS test pattern seed B
               when "10100" => -- 3.40, 10GBASE-R PCS test pattern seed B
               -- TODO:
               -- 1.1501    PRBS pattern testing control 45.2.1.96
               -- 1.1510    Square wave testing control 45.2.1.97
               when others => null;
            end case;
         end if;
      end if;
      end if;
   end if;
end process;

process(MI_CLK)
begin
   if MI_CLK'event and MI_CLK = '1' then
      if (r333_rd = '1') and (MI_RD = '1') then
         ber_count_l    <= ber_count_r(21 downto 6);
         blk_err_cntr_l <= blk_err_cntr_r(21 downto 8);
      end if;
   end if;
end process;

process(MI_CLK)
begin
   if MI_CLK'event and MI_CLK = '1' then
      -- PCS status latching flags --------------
      -- pcs block lock - latching low
      if (pcs_blk_lock_g = '0') then
         pcs_blk_lock_l <= '0';
      elsif (r333_rd_r = '1') then
         pcs_blk_lock_l <= '1';
      end if;
      -- pcs high BER - latching high
      if (pcs_hi_ber = '1') then
         pcs_hi_ber_l <= '1';
      elsif (r333_rd_r = '1') then
         pcs_hi_ber_l <= '0';
      end if;
      -- pcs RX link status - latching low
      if pcs_rxl_stat = '0' then
         pcs_rxl_stat_l <= '0';
      elsif (r301_rd_r) = '1' then
         pcs_rxl_stat_l <= '1';
      end if;
      -- pcs fault - latching high
      if pcs_fault = '1' then
         pcs_fault_l <= '1';
      elsif (r308_rd_r) = '1' then
         pcs_fault_l <= '0';
      end if;

      if fec_hi_ser_sync = '1' then
         fec_hi_ser_l <= '1';
      elsif (r1201_rd_r) = '1' then
         fec_hi_ser_l <= '0';
      end if;

   end if;
end process;

-- Outputs signals (MI_CLK clock domain)
SCR_BYPASS     <= scr_bypass_r;
PCS_LPBCK      <= pcs_lpbk;
PCS_RESET      <= pcs_rst;
PMA_LPBCK      <= pma_loc_lpbk;
PMA_REM_LPBCK  <= pma_rem_lpbk;
PMA_RESET      <= pma_rst;
PMA_LOPWR      <= low_pwr;
PMA_TX_DIS     <= tx_dis(PMA_TX_DIS'range) when tx_dis_g = '0' else
                 (others => '1');
PMA_CONTROL    <= pma_control_r;
PMA_PRECURSOR  <= pma_precursor_r;
PMA_POSTCURSOR <= pma_postcursor_r;
PMA_DRIVE      <= pma_drive_r;

-- Extend ouput CLR pulses to be used in slower clock domains
GEN_EXT_BER_CLR: for i in BIP_ERR_CLR'range generate
   EXT_BIP_ERR_CLR: entity work.PULSE_EXTEND port map (CLK => MI_CLK, I => r3200_rd_r(i), O => BIP_ERR_CLR(i));
end generate;
EXT_BER_CLR: entity work.PULSE_EXTEND port map (CLK => MI_CLK, I => r333_rd_r, O => BER_COUNT_CLR);
EXT_BLK_CLR: entity work.PULSE_EXTEND port map (CLK => MI_CLK, I => r333_rd_r, O => BLK_ERR_CLR);
EXT_FEC_SYM_ERR_CLR0:   entity work.PULSE_EXTEND port map (CLK => MI_CLK, I => r1211_rd_r, O => FEC_SYM_ERR_CLR(0));
EXT_FEC_SYM_ERR_CLR1:   entity work.PULSE_EXTEND port map (CLK => MI_CLK, I => r1213_rd_r, O => FEC_SYM_ERR_CLR(1));
EXT_FEC_SYM_ERR_CLR2:   entity work.PULSE_EXTEND port map (CLK => MI_CLK, I => r1215_rd_r, O => FEC_SYM_ERR_CLR(2));
EXT_FEC_SYM_ERR_CLR3:   entity work.PULSE_EXTEND port map (CLK => MI_CLK, I => r1217_rd_r, O => FEC_SYM_ERR_CLR(3));
EXT_FEC_COR_ERR_CLR:    entity work.PULSE_EXTEND port map (CLK => MI_CLK, I => r1203_rd_r, O => FEC_COR_ERR_CLR);
EXT_FEC_UNCOR_ERR_CLR:  entity work.PULSE_EXTEND port map (CLK => MI_CLK, I => r1205_rd_r, O => FEC_UNCOR_ERR_CLR);

-- RS-FEC control outputs
FEC_TX_EN  <= fec_en_r and fec_tx_en_r;
FEC_RX_EN  <= fec_en_r and fec_rx_en_r;
FEC_COR_EN <= not fec_cor_bypass_r;
FEC_IND_EN <= not fec_ind_bypass_r;

end behavioral;
