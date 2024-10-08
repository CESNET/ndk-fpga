-- rx_path_40G.vhd : 40GBASE-R PCS - RX module, top level
-- Copyright (C) 2010-2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity rx_path_40g is
    generic (
        DEVICE        : string  := "ULTRASCALE"; --! "VIRTEX6", "7SERIES", "ULTRASCALE"
        SINGLE_LANE   : boolean := false -- Enable single lane mode PCS (10G, 25G mode)
    );
    port (
        -- PCS/MAC
        RESET_PCS     : in std_logic;
        CLK           : in std_logic; -- XLGMII clock, 156.25MHz
        XLGMII_RXD    : out std_logic_vector(255 downto 0); -- RX data
        XLGMII_RXC    : out std_logic_vector(31 downto 0);  -- RX command
        -- PMA interface
        RESET_PMA     : in std_logic;                     -- PMA clock domain reset
        RX_OK         : out std_logic;                    -- RX data valid (decoded ok)
        RXCLK         : in std_logic;                     -- PMA RX clock - 161.1328125 MHz
        RXD0          : in std_logic_vector(65 downto 0); -- RX data from PMA - PCS lane 0
        RXD1          : in std_logic_vector(65 downto 0); -- RX data from PMA - PCS lane 1
        RXD2          : in std_logic_vector(65 downto 0); -- RX data from PMA - PCS lane 2
        RXD3          : in std_logic_vector(65 downto 0); -- RX data from PMA - PCS lane 3
        RXD_VALID     : in std_logic_vector(3 downto 0);  -- RX data valid = clock enable for each lane
        -- Status ports
        BLK_LOCK      : in  std_logic_vector(3 downto 0);  -- Block sync lock for each lane, CLK domain
        HI_BER        : out std_logic;                     -- Block sync HI BER for each lane, RXCLK domain
        LINKSTATUS    : out std_logic;                     -- align_locked and not hi_ber, RXCLK domain
        BER_COUNT     : out std_logic_vector(21 downto 0); -- BER monitor number of errored block (all lanes), RXCLK domain
        BER_CNT_CLR   : in std_logic := '0';               -- Clear BER counter in the block sync, async
        BLK_ERR_CNTR  : out std_logic_vector(21 downto 0); -- Block decore error counter, CLK domain
        BLK_ERR_CLR   : in std_logic := '0';               -- Clear block err counter in the decoder
        SCR_BYPASS    : in std_logic := '0';               -- Bypass the descrambler
        --
        LANE_MAP      : out std_logic_vector((4*5)-1 downto 0); --
        LANES_ALIGNED : out std_logic_vector(4-1 downto 0);     --
        ALIGN_LOCKED  : out std_logic;
        BIP_ERR_CNTRS : out std_logic_vector((4*16)-1 downto 0); -- BIP error counters
        BIP_ERR_CLR   : in  std_logic_vector(4-1 downto 0);
        DEC_ERROR     : out std_logic_vector(4-1 downto 0);
        SEQ_ERROR     : out std_logic_vector(4-1 downto 0);
        -- Debug ports
        AM_CNTR_O     : out std_logic;
        AM_FOUND_O    : out std_logic_vector(3 downto 0); --
        BIP_ERR_O     : out std_logic_vector(3 downto 0); --
        FIFO_DV_O     : out std_logic_vector(3 downto 0); --
        FIFO_RD_O     : out std_logic_vector(3 downto 0); --
        FIFO_FULL_O   : out std_logic_vector(3 downto 0); --
        FIFO_EMPTY_O  : out std_logic_vector(3 downto 0); --
        RXD_O         : out std_logic_vector(4*66-1 downto 0); --
        RXD_CE        : out std_logic;
        DEC_STATE     : out std_logic_vector(4*3-1 downto 0) -- Decoder state
    );
end rx_path_40g;

-- ----------------------------------------------------------------------------
--             Architecture declaration  --  ComboLXT Top Level              --
-- ----------------------------------------------------------------------------
architecture structural of rx_path_40g is

    constant NUM_LANES : natural := 4;

    signal reset_n           : std_logic;
    signal rxd               : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal zeros             : std_logic_vector(127 downto 0);
    signal data_to_scr       : std_logic_vector(64*NUM_LANES-1 downto 0);
    signal data_from_scr     : std_logic_vector(64*NUM_LANES-1 downto 0);
    signal data_to_ber_mon   : std_logic_vector(2*NUM_LANES-1 downto 0);
    signal data_to_fifo      : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal data_from_fifo    : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal rxd_aligned       : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal rxd_aligned_ce    : std_logic;
    signal rx_sync_ce        : std_logic_vector(NUM_LANES-1 downto 0);
    signal hi_ber_i          : std_logic;
    signal hi_ber_xclk       : std_logic;
    signal regasync_blk_lock : std_logic_vector(NUM_LANES-1 downto 0);
    signal blk_lock_xclk     : std_logic_vector(NUM_LANES-1 downto 0);
    signal blk_lock_all      : std_logic;
    signal linkstatus_i      : std_logic;
    signal align_locked_i    : std_logic;
    signal align_locked_xclk : std_logic;
    signal bip_err_clr_rxclk : std_logic_vector(BIP_ERR_CLR'range);
    signal clear_ber_count   : std_logic;
    signal blk_err_clr_i     : std_logic;
    signal scr_bypass_i      : std_logic;
    signal blk_err_cntr_i    : std_logic_vector(BLK_ERR_CNTR'range);
    signal valid_code        : std_logic_vector(NUM_LANES-1 downto 0);

begin

   zeros <= (others => '0');

   reset_n <= not RESET_PMA;

   rxd   <= RXD3 & RXD2 & RXD1 & RXD0;

   -- Control/status clock domain crossing from/to MGMT---------------------------
   GEN_BIPCLR_SYNC: for i in BIP_ERR_CLR'range generate
       ASYNC_CROSS_BIPCLR: entity work.ASYNC_OPEN_LOOP
       generic map(IN_REG  => false, TWO_REG => true)
       port map(
           ACLK     => '0',
           ARST     => '0',
           ADATAIN  => BIP_ERR_CLR(i),
           --
           BCLK     => RXCLK,
           BRST     => '0',
           BDATAOUT => bip_err_clr_rxclk(i)
       );
   end generate;

   ASYNC_CROSS_BERCLR: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map(
       ACLK     => '0',
       ARST     => '0',
       ADATAIN  => BER_CNT_CLR,
       --
       BCLK     => RXCLK,
       BRST     => '0',
       BDATAOUT => clear_ber_count
   );

   ASYNC_CROSS_BLKERR_CLR: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map(
       ACLK     => '0',
       ARST     => '0',
       ADATAIN  => BLK_ERR_CLR,
       --
       BCLK     => CLK,
       BRST     => '0',
       BDATAOUT => blk_err_clr_i
   );

   ASYNC_CROSS_SCR_BYP: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map(
       ACLK     => '0',
       ARST     => '0',
       ADATAIN  => SCR_BYPASS,
       --
       BCLK     => RXCLK,
       BRST     => '0',
       BDATAOUT => scr_bypass_i
   );

   -- Clock domain crossing - internal signals --------------------

   GEN_BLK_LOCK_SYNC: for i in BLK_LOCK'range generate
       ASYNC_CROSS_BL: entity work.ASYNC_OPEN_LOOP
       generic map(IN_REG  => false, TWO_REG => true)
       port map(
           ACLK     => RXCLK,
           ARST     => '0',
           ADATAIN  => BLK_LOCK(i),
           --
           BCLK     => CLK,
           BRST     => '0',
           BDATAOUT => blk_lock_xclk(i)
       );
   end generate;

   ASYNC_CROSS_HIB: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map(

       ACLK     => RXCLK,
       ARST     => '0',
       ADATAIN  => hi_ber_i,
       --
       BCLK     => CLK,
       BRST     => '0',
       BDATAOUT => hi_ber_xclk
   );

   ASYNC_CROSS_AL: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG  => false, TWO_REG => true)
   port map(

       ACLK     => RXCLK,
       ARST     => '0',
       ADATAIN  => align_locked_i,
       --
       BCLK     => CLK,
       BRST     => '0',
       BDATAOUT => align_locked_xclk
   );

   -- =========================================================================
   -- Lane aligner
   -- =========================================================================

   ALIGN_SHIFT: if (not SINGLE_LANE) generate

       ALIGN: entity work.lane_align_deprecated(behavioral)
       generic map (
           SHIFTS => 16         -- shift register width = lanes skew size
       )
       port map (
           RESET         => RESET_PMA,         --
           CLK           => RXCLK,
           EN            => RXD_VALID,         -- Input enable for each lane
           D             => RXD,               -- Input data for each lane
           Q             => rxd_aligned,       -- Output data for each lane
           QV            => rxd_aligned_ce,    -- Otput data valid
           BLK_LOCK      => BLK_LOCK,          -- Block lock for each lane
           -- Status ports
           LOCKED        => align_locked_i,    -- valid mark found on each lane
           LANE_MAP      => LANE_MAP,          -- output mapping for each lane
           LANES_ALIGNED => LANES_ALIGNED,     -- alignment confirmed for eac line
           BIP_ERR_CNTRS => BIP_ERR_CNTRS,     -- BIP error counters out
           CLR_ERR_CNTRS => bip_err_clr_rxclk, -- BIP error counters reset
           --
           am_match_DBG(11 downto 0)  => DEC_STATE,
           am_match_DBG(15 downto 12) => FIFO_RD_O,
           am_lock_DBG                => FIFO_DV_O,
           am_cntrs_end_DBG           => FIFO_FULL_O,
           am_found_DBG               => AM_FOUND_O,
           bip_match_DBG              => FIFO_EMPTY_O,
           bip_err_DBG                => BIP_ERR_O
       );
   end generate;

   -- Single lane mode
   NO_ALIGN: if SINGLE_LANE generate
       align_locked_i <= '1';
       LANE_MAP       <= (others => '0');
       LANES_ALIGNED  <= (others => '1');
       BIP_ERR_CNTRS  <= (others => '0');

       rxd_aligned    <= RXD;
       rxd_aligned_ce <= RXD_VALID(0);

   end generate;


   GEN_BM_DATA: for i in 0 to NUM_LANES-1 generate
       data_to_ber_mon((i+1)*2-1 downto i*2) <= rxd_aligned(66*i+1 downto i*66); -- sync headers only
   end generate;

   -- =========================================================================
   -- BER monitor
   -- =========================================================================

   BER_MONITOR: entity work.ber_mon
   generic map (
       NUM_LANES       => 4
   )
   port map (
       RESET         => RESET_PMA,
       CLK           => RXCLK,
       CE            => rxd_aligned_ce,
       SH            => data_to_ber_mon,
       --
       BER_CNT       => open,
       BER_COUNT_CLR => clear_ber_count,
       BER_COUNT     => BER_COUNT,
       HI_BER        => hi_ber_i
   );

   -- =========================================================================
   -- Descrambler
   -- =========================================================================

   GEN_SCR_DATA: for i in 0 to NUM_LANES-1 generate
       data_to_scr((i+1)*64-1 downto i*64) <= rxd_aligned(66*(i+1)-1 downto i*66+2); -- Exclude sync bits
   end generate;

   DESCRAMBLE: entity work.descrambler_gen
   generic map (
       WIDTH => NUM_LANES*64
   )
   port map (
       RESET  => RESET_PMA,
       CLK    => RXCLK,
       EN     => rxd_aligned_ce,
       BYPASS => scr_bypass_i,
       SEED   => zeros(57 downto 0),
       D      => data_to_scr,
       Q      => data_from_scr
   );

   GEN_FIFO_DATA: for i in 0 to NUM_LANES-1 generate
       data_to_fifo((i+1)*66-1 downto i*66+2) <= data_from_scr(64*(i+1)-1 downto i*64);
       data_to_fifo(i*66+1 downto i*66) <= rxd_aligned(66*i+1 downto i*66); -- Add sync bits
   end generate;

   -- =========================================================================
   -- Rate compensating FIFO
   -- =========================================================================

   FIFO: entity work.pcs_rx_fifo
   generic map (
       NUM_LANES => NUM_LANES,
       DEVICE    => DEVICE
   )
   port map (
       RESET_D    => RESET_PMA,
       CLK_D      => RXCLK,
       WE         => rxd_aligned_ce,
       D          => data_to_fifo,
       --
       RESET_Q    => RESET_PCS,
       CLK_Q      => CLK,
       Q          => data_from_fifo,
       --
       FIFO_FULL  => open, -- FIFO_FULL_O(0),
       FIFO_EMPTY => open  -- FIFO_EMPTY_O(0)
   );

   -- All lanes are locked
   blk_lock_all <= blk_lock_xclk(0) and blk_lock_xclk(1) and blk_lock_xclk(2) and blk_lock_xclk(3) and align_locked_xclk;

   -- =========================================================================
   -- 66/44 GBASE-R decoder
   -- =========================================================================
    decode_i: entity work.gbaser_decode
    generic map (
        LANES => 4
    )
    port map (
        RESET        => RESET_PCS,
        CLK          => CLK,
        -- PMA interface ----------------------------
        D            => data_from_fifo,
        -- RS/MAC interface -------------------------
        RXD          => XLGMII_RXD,
        RXC          => XLGMII_RXC,
        -- Control/status
        BLK_LOCK     => blk_lock_all,
        HI_BER       => hi_ber_xclk,
        BLK_ERR_CNTR => BLK_ERR_CNTR,
        BLK_ERR_CLR  => blk_err_clr_i,
        DEC_ERROR    => DEC_ERROR,
        SEQ_ERROR    => SEQ_ERROR,
        VALID_CODE   => valid_code
    );

   linkstatus_i <= align_locked_i and (not hi_ber_i);

   -- =========================================================================
   -- Others
   -- =========================================================================

   ALIGN_LOCKED <= align_locked_i;
   HI_BER       <= hi_ber_i;
   LINKSTATUS   <= linkstatus_i;
   RXD_O        <= rxd; -- rxd_aligned;
   RXD_CE       <= RXD_VALID(0);
   BLK_ERR_CNTR <= BLK_ERR_CNTR_i;
   RX_OK        <= linkstatus_i and (and valid_code);

end structural;

