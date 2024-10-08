-- mfb_speed_meter.vhd: MFB speed meter
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MFB_SPEED_METER is
   generic(
      -- =================
      -- MFB CONFIGURATION
      -- =================

      REGIONS         : natural := 2;
      REGION_SIZE     : natural := 8;
      BLOCK_SIZE      : natural := 8;
      ITEM_WIDTH      : natural := 8;

      -- =========================
      -- SPEED METER CONFIGURATION
      -- =========================

      -- Set time of speed test (time = (2^CNT_TICKS_WIDTH)-1 in clock ticks).
      CNT_TICKS_WIDTH : natural := 24;
      -- Set width of valid bytes counter. Optimum and MINIMUM value is:
      -- log2(((2^CNT_TICKS_WIDTH)-1)*REGIONS*REGION_SIZE*BLOCK_SIZE)
      CNT_BYTES_WIDTH : natural := 32;
      -- Set width of packet counters.
      CNT_PKTS_WIDTH  : natural := 32;
      -- Disable Speed Meter when CNT_CLEAR is asserted (enable with next SOF).
      DISABLE_ON_CLR  : boolean := true;
      -- Set to true to count incoming SOFs and EOFs.
      COUNT_PACKETS   : boolean := false;
      -- Set to true to add SOFs and EOFs from the currently arriving word to the total sums.
      -- Set to false to count only accepted words.
      ADD_ARR_PKTS    : boolean := false
   );
   port(
      -- =================
      -- CLOCK AND RESET
      -- =================

      CLK           : in  std_logic;
      RST           : in  std_logic;

      -- =========================
      -- RX MFB CONTROL INTERFACE
      -- =========================

      RX_SOF_POS    : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      RX_EOF_POS    : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      RX_SOF        : in  std_logic_vector(REGIONS-1 downto 0);
      RX_EOF        : in  std_logic_vector(REGIONS-1 downto 0);
      RX_SRC_RDY    : in  std_logic;
      RX_DST_RDY    : in  std_logic;

      -- =========================
      -- SPEED METER COUNTERS
      -- =========================

      -- counter of clock ticks
      CNT_TICKS     : out std_logic_vector(CNT_TICKS_WIDTH-1 downto 0);
      -- maximum value flag of clock ticks counter, when CNT_TICKS_MAX=1 speed test is done
      CNT_TICKS_MAX : out std_logic;
      -- counter of valid bytes
      CNT_BYTES     : out std_logic_vector(CNT_BYTES_WIDTH-1 downto 0);
      -- counter of packet SOFs
      CNT_PKT_SOFS  : out std_logic_vector(CNT_PKTS_WIDTH-1 downto 0);
      -- counter of packet EOFs
      CNT_PKT_EOFS  : out std_logic_vector(CNT_PKTS_WIDTH-1 downto 0);
      -- reset all counters
      CNT_CLEAR     : in  std_logic
   );
end MFB_SPEED_METER;

architecture FULL of MFB_SPEED_METER is

   constant REGION_BYTES     : natural := REGION_SIZE*BLOCK_SIZE;
   constant SOF_POS_SIZE     : natural := max(1,log2(REGION_SIZE));
   constant EOF_POS_SIZE     : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));
   constant BLOCK_WIDTH      : natural := log2(BLOCK_SIZE);
   constant WORD_BYTES_WIDTH : natural := log2(REGIONS*REGION_SIZE*BLOCK_SIZE+1);
   constant BLOCK_WIDTH_GND  : std_logic_vector(EOF_POS_SIZE-SOF_POS_SIZE-1 downto 0) := (others => '0');

   type uns_array_t is array (natural range <>) of unsigned;

   signal rx_sof_pos_reg       : std_logic_vector(REGIONS*SOF_POS_SIZE-1 downto 0);
   signal rx_eof_pos_reg       : std_logic_vector(REGIONS*EOF_POS_SIZE-1 downto 0);
   signal rx_sof_reg           : std_logic_vector(REGIONS-1 downto 0);
   signal rx_eof_reg           : std_logic_vector(REGIONS-1 downto 0);
   signal rx_src_rdy_reg       : std_logic;
   signal rx_src_rdy_reg2      : std_logic;
   signal rx_dst_rdy_reg       : std_logic;
   signal rx_dst_rdy_reg2      : std_logic;

   signal valid_word           : std_logic;
   signal valid_word2          : std_logic;
   signal any_sof              : std_logic;
   signal any_eof              : std_logic;
   signal enable_reg           : std_logic;

   signal sof_pos_arr          : slv_array_t(REGIONS-1 downto 0)(SOF_POS_SIZE-1 downto 0);
   signal eof_pos_arr          : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);
   signal sof_pos_ext_arr      : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);

   signal incomplete_frame     : std_logic_vector(REGIONS downto 0);
   signal frame_state_reg      : slv_array_t(REGIONS-1 downto 0)(3-1 downto 0);
   signal cnt_reg_en           : std_logic;

   signal bytes_cnt_addend_011 : uns_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE downto 0);
   signal bytes_cnt_addend_100 : uns_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE downto 0);
   signal bytes_cnt_addend_110 : uns_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE downto 0);
   signal bytes_cnt_addend_111 : uns_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE downto 0);

   signal bytes_cnt            : uns_array_t(REGIONS downto 0)(WORD_BYTES_WIDTH-1 downto 0);
   signal bytes_cnt_reg        : unsigned(CNT_BYTES_WIDTH-1 downto 0);

   signal sof_sum_one          : std_logic_vector(CNT_PKTS_WIDTH-1 downto 0);
   signal sof_sum_one_vld      : std_logic;
   signal sof_cnt              : std_logic_vector(CNT_PKTS_WIDTH-1 downto 0);
   signal sof_cnt_reg          : std_logic_vector(CNT_PKTS_WIDTH-1 downto 0);
   signal sof_cnt_total        : std_logic_vector(CNT_PKTS_WIDTH-1 downto 0);
   signal eof_sum_one          : std_logic_vector(CNT_PKTS_WIDTH-1 downto 0);
   signal eof_sum_one_vld      : std_logic;
   signal eof_cnt              : std_logic_vector(CNT_PKTS_WIDTH-1 downto 0);
   signal eof_cnt_reg          : std_logic_vector(CNT_PKTS_WIDTH-1 downto 0);
   signal eof_cnt_total        : std_logic_vector(CNT_PKTS_WIDTH-1 downto 0);

   signal ticks_cnt_reg        : unsigned(CNT_TICKS_WIDTH-1 downto 0);
   signal ticks_cnt_reg_max    : std_logic;

begin

   -- --------------------------------------------------------------------------
   --  INPUT MFB REGISTER
   -- --------------------------------------------------------------------------

   rx_mfb_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         rx_sof_pos_reg <= RX_SOF_POS;
         rx_eof_pos_reg <= RX_EOF_POS;
         rx_sof_reg     <= RX_SOF;
         rx_eof_reg     <= RX_EOF;
      end if;
   end process;

   rx_mfb_vld_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RST = '1') then
            rx_src_rdy_reg  <= '0';
            rx_src_rdy_reg2 <= '0';
            rx_dst_rdy_reg  <= '0';
            rx_dst_rdy_reg2 <= '0';
         end if;
         rx_src_rdy_reg  <= RX_SRC_RDY;
         rx_src_rdy_reg2 <= rx_src_rdy_reg;
         rx_dst_rdy_reg  <= RX_DST_RDY;
         rx_dst_rdy_reg2 <= rx_dst_rdy_reg;
      end if;
   end process;

   valid_word  <= rx_src_rdy_reg  and rx_dst_rdy_reg;
   valid_word2 <= rx_src_rdy_reg2 and rx_dst_rdy_reg2;

   -- --------------------------------------------------------------------------
   --  SOF POS AND EOF POS ARRAYS
   -- --------------------------------------------------------------------------

   position_arr_g : for i in 0 to REGIONS-1 generate
      sof_pos_arr(i)     <= rx_sof_pos_reg((i+1)*SOF_POS_SIZE-1 downto i*SOF_POS_SIZE);
      eof_pos_arr(i)     <= rx_eof_pos_reg((i+1)*EOF_POS_SIZE-1 downto i*EOF_POS_SIZE);
      sof_pos_ext_arr(i) <= sof_pos_arr(i) & BLOCK_WIDTH_GND;
   end generate;

   -- --------------------------------------------------------------------------
   --  FRAME STATE LOGIC
   -- --------------------------------------------------------------------------

   incomplete_frame_g : for r in 0 to REGIONS-1 generate
      incomplete_frame(r+1) <= (rx_sof_reg(r) and not rx_eof_reg(r) and not incomplete_frame(r)) or
                               (rx_sof_reg(r) and rx_eof_reg(r) and incomplete_frame(r)) or
                               (not rx_sof_reg(r) and not rx_eof_reg(r) and incomplete_frame(r));
   end generate;

   incomplete_frame_last_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RST = '1') then
            incomplete_frame(0) <= '0';
         elsif (valid_word = '1') then
            incomplete_frame(0) <= incomplete_frame(REGIONS);
         end if;
      end if;
   end process;

   frame_state_g : for r in 0 to REGIONS-1 generate
      frame_state_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            frame_state_reg(r) <= rx_sof_reg(r) & rx_eof_reg(r) & incomplete_frame(r);
         end if;
      end process;
   end generate;

   -- --------------------------------------------------------------------------
   --  ENABLE REGISTER
   -- --------------------------------------------------------------------------

   any_sof <= or rx_sof_reg;
   any_eof <= or rx_eof_reg;

   -- counters start with first SOF
   enable_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if ((CNT_CLEAR = '1' and DISABLE_ON_CLR = true) or RST = '1') then
            enable_reg <= '0';
         elsif (valid_word = '1' and any_sof = '1') then
            enable_reg <= '1';
         end if;
      end if;
   end process;

   -- --------------------------------------------------------------------------
   --  BYTES COUNTER LOGIC
   -- --------------------------------------------------------------------------

   bytes_cnt_addend_g : for r in 0 to REGIONS-1 generate
      bytes_cnt_addend_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            bytes_cnt_addend_011(r) <= unsigned('0' & eof_pos_arr(r)) + 1;
            bytes_cnt_addend_100(r) <= REGION_BYTES - unsigned('0' & sof_pos_ext_arr(r));
            bytes_cnt_addend_110(r) <= unsigned('0' & eof_pos_arr(r)) + 1 - unsigned(sof_pos_ext_arr(r));
            bytes_cnt_addend_111(r) <= unsigned('0' & eof_pos_arr(r)) + 1 + (REGION_BYTES - unsigned(sof_pos_ext_arr(r)));
         end if;
      end process;
   end generate;

   bytes_cnt(0) <= (others => '0');

   bytes_cnt_logic_g : for r in 0 to REGIONS-1 generate
      bytes_cnt_logic_p : process (frame_state_reg, bytes_cnt, bytes_cnt_addend_011, bytes_cnt_addend_100, bytes_cnt_addend_110, bytes_cnt_addend_111)
      begin
         case (frame_state_reg(r)) is
            when "001" =>
               bytes_cnt(r+1) <= bytes_cnt(r) + REGION_BYTES;
            when "011" =>
               bytes_cnt(r+1) <= bytes_cnt(r) + bytes_cnt_addend_011(r);
            when "100" =>
               bytes_cnt(r+1) <= bytes_cnt(r) + bytes_cnt_addend_100(r);
            when "110" =>
               bytes_cnt(r+1) <= bytes_cnt(r) + bytes_cnt_addend_110(r);
            when "111" =>
               bytes_cnt(r+1) <= bytes_cnt(r) + bytes_cnt_addend_111(r);
            when others =>
               bytes_cnt(r+1) <= bytes_cnt(r);
         end case;
      end process;
   end generate;

   -- --------------------------------------------------------------------------
   --  BYTES COUNTER REGISTER
   -- --------------------------------------------------------------------------

   bytes_cnt_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (CNT_CLEAR = '1' or RST = '1') then
            bytes_cnt_reg <= (others => '0');
         elsif (cnt_reg_en = '1' and valid_word2 = '1') then
            bytes_cnt_reg <= bytes_cnt_reg + bytes_cnt(REGIONS);
         end if;
      end if;
   end process;

   -- --------------------------------------------------------------------------
   --  PACKET COUNTERS LOGIC
   -- --------------------------------------------------------------------------

   count_pkts_g: if COUNT_PACKETS = true generate

      sof_sum_one_i: entity work.SUM_ONE
      generic map (
         INPUT_WIDTH  => REGIONS,
         OUTPUT_WIDTH => CNT_PKTS_WIDTH,
         OUTPUT_REG   => false
      )
      port map (
         CLK      => CLK,
         RESET    => RST,

         DIN      => rx_sof_reg,
         DIN_MASK => (others => '1'),
         DIN_VLD  => rx_src_rdy_reg,

         DOUT     => sof_sum_one,
         DOUT_VLD => sof_sum_one_vld
      );

      eof_sum_one_i: entity work.SUM_ONE
      generic map (
         INPUT_WIDTH  => REGIONS,
         OUTPUT_WIDTH => CNT_PKTS_WIDTH,
         OUTPUT_REG   => false
      )
      port map (
         CLK      => CLK,
         RESET    => RST,

         DIN      => rx_eof_reg,
         DIN_MASK => (others => '1'),
         DIN_VLD  => rx_src_rdy_reg,

         DOUT     => eof_sum_one,
         DOUT_VLD => eof_sum_one_vld
      );

      -- --------------------------------------------------------------------------
      --  PACKET COUNTERS REGISTERS
      -- --------------------------------------------------------------------------

      sof_cnt_reg_p: process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (CNT_CLEAR = '1' or RST = '1') then
               sof_cnt_reg <= (others => '0');
            elsif (any_sof = '1' and valid_word = '1' and ticks_cnt_reg_max = '0') then
               sof_cnt_reg <= sof_cnt_total;
            end if;
         end if;
      end process;

      sof_cnt       <= sof_sum_one when sof_sum_one_vld = '1' else (others => '0');
      sof_cnt_total <= std_logic_vector(unsigned(sof_cnt) + unsigned(sof_cnt_reg));

      eof_cnt_reg_p: process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (CNT_CLEAR = '1' or RST = '1') then
               eof_cnt_reg <= (others => '0');
            elsif (any_eof = '1' and valid_word = '1' and ticks_cnt_reg_max = '0') then
               eof_cnt_reg <= eof_cnt_total;
            end if;
         end if;
      end process;

      eof_cnt       <= eof_sum_one when eof_sum_one_vld = '1' else (others => '0');
      eof_cnt_total <= std_logic_vector(unsigned(eof_cnt) + unsigned(eof_cnt_reg));

   else generate

      sof_cnt_reg   <= (others => '0');
      sof_cnt_total <= (others => '0');
      eof_cnt_reg   <= (others => '0');
      eof_cnt_total <= (others => '0');

   end generate;

   -- --------------------------------------------------------------------------
   --  TICKS COUNTER REGISTER
   -- --------------------------------------------------------------------------

   ticks_cnt_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (CNT_CLEAR = '1' or RST = '1') then
            ticks_cnt_reg <= (others => '0');
         elsif (cnt_reg_en = '1') then
            ticks_cnt_reg <= ticks_cnt_reg + 1;
         end if;
      end if;
   end process;

   ticks_cnt_reg_max <= and ticks_cnt_reg;
   cnt_reg_en <= enable_reg and not ticks_cnt_reg_max;

   -- --------------------------------------------------------------------------
   --  OUTPUTS ASSIGNMENT
   -- --------------------------------------------------------------------------

   CNT_BYTES     <= std_logic_vector(bytes_cnt_reg);
   CNT_TICKS     <= std_logic_vector(ticks_cnt_reg);
   CNT_TICKS_MAX <= ticks_cnt_reg_max;

   sum_pkts_g: if ADD_ARR_PKTS = false generate
      CNT_PKT_SOFS <= sof_cnt_reg;
      CNT_PKT_EOFS <= eof_cnt_reg;
   else generate
      CNT_PKT_SOFS <= sof_cnt_total;
      CNT_PKT_EOFS <= eof_cnt_total;
   end generate;

end architecture;
