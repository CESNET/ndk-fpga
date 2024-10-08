-- ptc_hdr_data_merge_hpai.vhd: PTC header data merge - header plan and insert
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity PTC_HDR_DATA_MERGE_HPAI is
   generic(
      -- =======================================================================
      -- MFB DATA BUS CONFIGURATION:
      -- =======================================================================
      -- Supported configuration is only MFB(2,1,8,32)
      MFB_REGIONS        : natural := 2;
      MFB_REGION_SIZE    : natural := 1;
      MFB_BLOCK_SIZE     : natural := 8;
      MFB_ITEM_WIDTH     : natural := 32;
      -- =======================================================================
      -- MVB HEADER BUS CONFIGURATION:
      -- =======================================================================
      -- Supported configuration is only MVB(2,128)
      MVB_ITEMS          : natural := 2;
      MVB_ITEM_WIDTH     : natural := 128;
      -- =======================================================================
      -- OTHER CONFIGURATION:
      -- =======================================================================
      -- Width of PCIe transaction size signal. Set Log2 of maximum supported
      -- PCIe transaction size (HDR + payload) in dwords
      TRANS_SIZE_WIDTH   : natural := 8;
      -- Set correct device type.
      DEVICE             : string  := "ULTRASCALE";
      -- Connected PCIe endpoint type ("H_TILE" or "P_TILE" or "R_TILE")
      ENDPOINT_TYPE      : string  := "H_TILE"
   );
   port(
      -- =======================================================================
      -- CLOCK AND RESET
      -- =======================================================================
      CLK                 : in  std_logic;
      RESET               : in  std_logic;
      -- =======================================================================
      -- INPUT MVB HEADER INTERFACE
      -- =======================================================================
      -- header of PCIe transaction
      RX_MVB_DATA         : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
      -- PCIe transaction length last and first DWORD byte enable (MSB -> last byte, LSB -> first byte)
      RX_MVB_BE           : in  std_logic_vector(MVB_ITEMS*8-1 downto 0);
      -- is PCIe transaction with payload
      RX_MVB_PAYLOAD      : in  std_logic_vector(MVB_ITEMS-1 downto 0);
      -- size of transaction payload, valid with RX_MVB_PAYLOAD
      RX_MVB_PAYLOAD_SIZE : in  std_logic_vector(MVB_ITEMS*TRANS_SIZE_WIDTH-1 downto 0);
      -- PCIe heade size type (Intel only) ('0' -> 96-bit type, '1' -> 128-bit type)
      RX_MVB_TYPE         : in  std_logic_vector(MVB_ITEMS-1 downto 0);
      -- valid of each header of PCIe transaction in MVB word
      RX_MVB_VLD          : in  std_logic_vector(MVB_ITEMS-1 downto 0);
      -- MVB word is valid
      RX_MVB_SRC_RDY      : in  std_logic;
      -- MVB destination is ready
      RX_MVB_DST_RDY      : out std_logic;
      -- =======================================================================
      -- OUTPUT MVB INTERFACE
      -- =======================================================================
      TX_MVB_DATA         : out std_logic_vector(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
      TX_MVB_VLD          : out std_logic_vector(MFB_REGIONS-1 downto 0);
    --TX_MVB_SRC_RDY      : out std_logic; -- only TX_MFB_SRC_RDY is used
    --TX_MVB_DST_RDY      : in  std_logic; -- only TX_MFB_DST_RDY is used
      -- =======================================================================
      -- OUTPUT MFB INTERFACE
      -- =======================================================================
      TX_MFB_DATA         : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      TX_MFB_SOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
      TX_MFB_EOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
      TX_MFB_SOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX_MFB_EOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX_MFB_BE           : out std_logic_vector(MFB_REGIONS*8-1 downto 0);
      TX_MFB_PAYLOAD      : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX_MFB_TYPE         : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX_MFB_SRC_RDY      : out std_logic;
      TX_MFB_DST_RDY      : in  std_logic
   );
end PTC_HDR_DATA_MERGE_HPAI;

architecture FULL of PTC_HDR_DATA_MERGE_HPAI is

   type uns_array_t is array (natural range <>) of unsigned;

   constant MFB_REGION_WIDTH    : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
   constant MFB_EOF_POS_WIDTH   : natural := max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));
   constant WORD_CNT_W          : natural := TRANS_SIZE_WIDTH - (log2(MFB_REGIONS) + MFB_EOF_POS_WIDTH);
   constant MVB_ITEM_PLUS_WIDTH : natural := MVB_ITEM_WIDTH + 8 + TRANS_SIZE_WIDTH + 1 + 1;
   -- On R-Tile for performance reasons, tx_stN_sop_i pulses can only be sent on segments 0 and/or 2 (st0 and/or st2).
   -- See Intel UG-20316 section 4.4.1.4. => ONE_PKT_PER_WORD = True on R-Tile...
   constant ONE_PKT_PER_WORD    : boolean := ((DEVICE = "STRATIX10") and (ENDPOINT_TYPE = "H_TILE")) or ((DEVICE = "AGILEX") and (ENDPOINT_TYPE = "R_TILE"));
   constant INTEL_DEVICE        : boolean := (DEVICE = "STRATIX10") or (DEVICE = "AGILEX");
   constant PTILE_RTILE_DEVICE  : boolean := (DEVICE = "STRATIX10" or DEVICE = "AGILEX") and (ENDPOINT_TYPE = "P_TILE" or ENDPOINT_TYPE = "R_TILE");
   constant FIFO_DEPTH          : natural := tsel(INTEL_DEVICE,32,16);

   signal s_rx_mvb_data_reg         : std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
   signal s_rx_mvb_be_reg           : std_logic_vector(MVB_ITEMS*8-1 downto 0);
   signal s_rx_mvb_payload_reg      : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal s_rx_mvb_payload_size_reg : std_logic_vector(MVB_ITEMS*TRANS_SIZE_WIDTH-1 downto 0);
   signal s_rx_mvb_type_reg         : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal s_rx_mvb_vld_reg          : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal s_rx_mvb_src_rdy_reg      : std_logic;

   signal s_rx_mvb_data_arr         : slv_array_t(MVB_ITEMS-1 downto 0)(MVB_ITEM_WIDTH-1 downto 0);
   signal s_rx_mvb_be_arr           : slv_array_t(MVB_ITEMS-1 downto 0)(8-1 downto 0);
   signal s_rx_mvb_be_arr_fixed     : slv_array_t(MVB_ITEMS-1 downto 0)(8-1 downto 0);
   signal s_rx_mvb_payload_size_arr : slv_array_t(MVB_ITEMS-1 downto 0)(TRANS_SIZE_WIDTH-1 downto 0);

   signal s_rx_mvb_data_plus_arr    : slv_array_t(MVB_ITEMS-1 downto 0)(MVB_ITEM_PLUS_WIDTH-1 downto 0);
   signal s_rx_mvb_data_plus        : std_logic_vector(MVB_ITEMS*MVB_ITEM_PLUS_WIDTH-1 downto 0);
   signal s_rx_mvb_vld              : std_logic_vector(MVB_ITEMS-1 downto 0);

   signal s_fifo_mvb_data_plus      : std_logic_vector(MFB_REGIONS*MVB_ITEM_PLUS_WIDTH-1 downto 0);
   signal s_fifo_mvb_vld            : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_fifo_mvb_dst_rdy        : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_fifo_mvb_data_plus_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(MVB_ITEM_PLUS_WIDTH-1 downto 0);
   signal s_fifo_mvb_data_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(MVB_ITEM_WIDTH-1 downto 0);
   signal s_fifo_mvb_be             : slv_array_t(MFB_REGIONS-1 downto 0)(8-1 downto 0);
   signal s_fifo_mvb_payload        : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_fifo_mvb_payload_size   : slv_array_t(MFB_REGIONS-1 downto 0)(TRANS_SIZE_WIDTH-1 downto 0);
   signal s_fifo_mvb_type           : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_fifo_mvb_accept         : std_logic_vector(MFB_REGIONS-1 downto 0);

   signal s_hdr_mux_sel             : uns_array_t(MFB_REGIONS downto 0)(log2(MFB_REGIONS+1)-1 downto 0);
   signal s_hdr_data_muxed_arr      : slv_array_t(MFB_REGIONS-1 downto 0)(MVB_ITEM_WIDTH-1 downto 0);
   signal s_hdr_be_muxed            : slv_array_t(MFB_REGIONS-1 downto 0)(8-1 downto 0);
   signal s_hdr_payload_muxed       : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_hdr_payload_size_muxed  : slv_array_t(MFB_REGIONS-1 downto 0)(TRANS_SIZE_WIDTH-1 downto 0);
   signal s_hdr_type_muxed          : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_hdr_vld_muxed           : std_logic_vector(MFB_REGIONS-1 downto 0);

   signal s_payload_len             : uns_array_t(MVB_ITEMS-1 downto 0)(TRANS_SIZE_WIDTH-1 downto 0);
   signal s_total_len               : uns_array_t(MVB_ITEMS-1 downto 0)(TRANS_SIZE_WIDTH-1 downto 0);

   signal s_word_cnt_reg            : unsigned(WORD_CNT_W-1 downto 0);
   signal s_word_cnt_reg_en         : std_logic;
   signal s_word_cnt_reg_load       : std_logic;
   signal s_word_cnt_per_region     : uns_array_t(MFB_REGIONS+1-1 downto 0)(WORD_CNT_W-1 downto 0);

   signal s_whole_pkt               : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_eof_offset_new          : uns_array_t(MFB_REGIONS-1 downto 0)(TRANS_SIZE_WIDTH-1 downto 0);
   signal s_eof_offset              : uns_array_t(MFB_REGIONS downto 0)(TRANS_SIZE_WIDTH-1 downto 0);
   signal s_eof_offset_word         : uns_array_t(MFB_REGIONS-1 downto 0)(WORD_CNT_W-1 downto 0);
   signal s_eof_offset_region       : uns_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGIONS)-1 downto 0);
   signal s_eof_pos                 : uns_array_t(MFB_REGIONS-1 downto 0)(MFB_EOF_POS_WIDTH-1 downto 0);

   signal s_eof_word_ok             : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_eof_region_ok           : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_eof_ok                  : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_eof_vld                 : std_logic_vector(MFB_REGIONS-1 downto 0);

   signal s_plan_en                 : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_plan_wait               : std_logic_vector(MFB_REGIONS downto 0);
   signal s_need_set_eof            : std_logic_vector(MFB_REGIONS downto 0);

   signal s_mfb_data                : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH-1 downto 0);
   signal s_mfb_eof_pos             : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_EOF_POS_WIDTH-1 downto 0);
   signal s_mfb_sof                 : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_mfb_eof                 : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_mfb_be                  : slv_array_t(MFB_REGIONS-1 downto 0)(8-1 downto 0);
   signal s_mfb_payload             : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_mfb_type                : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_mfb_src_rdy             : std_logic;

   signal s_tx_mfb_data             : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
   signal s_tx_mfb_sof_pos          : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
   signal s_tx_mfb_eof_pos          : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
   signal s_tx_mfb_sof              : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_tx_mfb_eof              : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_tx_mfb_be               : std_logic_vector(MFB_REGIONS*8-1 downto 0);
   signal s_tx_mfb_payload          : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_tx_mfb_type             : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_tx_mfb_src_rdy          : std_logic;

begin

   assert (DEVICE = "STRATIX10" OR DEVICE = "AGILEX" OR DEVICE = "ULTRASCALE" OR DEVICE = "7SERIES")
      report "PTC_HDR_DATA_MERGE_HPAI: unsupported device!" severity failure;

   rx_mvb_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RX_MVB_DST_RDY = '1') then
            s_rx_mvb_data_reg         <= RX_MVB_DATA;
            s_rx_mvb_be_reg           <= RX_MVB_BE;
            s_rx_mvb_payload_reg      <= RX_MVB_PAYLOAD;
            s_rx_mvb_payload_size_reg <= RX_MVB_PAYLOAD_SIZE;
            s_rx_mvb_type_reg         <= RX_MVB_TYPE;
            s_rx_mvb_vld_reg          <= RX_MVB_VLD;
         end if;
      end if;
   end process;

   rx_mvb_vld_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_rx_mvb_src_rdy_reg <= '0';
         elsif (RX_MVB_DST_RDY = '1') then
            s_rx_mvb_src_rdy_reg <= RX_MVB_SRC_RDY;
         end if;
      end if;
   end process;

   -----------------------------------------------------------------------------
   -- MVB HEADER FIFOX MULTI
   -----------------------------------------------------------------------------

   s_rx_mvb_data_arr <= slv_array_downto_deser(s_rx_mvb_data_reg,MVB_ITEMS,MVB_ITEM_WIDTH);
   s_rx_mvb_be_arr <= slv_array_downto_deser(s_rx_mvb_be_reg,MVB_ITEMS,8);
   s_rx_mvb_be_arr_fixed <= (others => (others => '0')) when INTEL_DEVICE else s_rx_mvb_be_arr;
   s_rx_mvb_payload_size_arr <= slv_array_downto_deser(s_rx_mvb_payload_size_reg,MVB_ITEMS,TRANS_SIZE_WIDTH);

   lenght_g : for r in 0 to MVB_ITEMS-1 generate
      -- get payload lenght in dwords (32b) from header data
      s_payload_len(r) <= unsigned(s_rx_mvb_payload_size_arr(r)) when (s_rx_mvb_payload_reg(r) = '1') else (others => '0');
      -- compute packet lenght from payload lenght in dwords (32b)
      s_total_len(r) <=      (s_payload_len(r) + 0) when PTILE_RTILE_DEVICE and s_rx_mvb_payload_reg(r)='1' -- write transaction with header separated from data
                        else (s_payload_len(r) + 1) when PTILE_RTILE_DEVICE                           -- read transaction with just separated header (1 invalid dword is still added to MFB, as it is impossible to create a 0 length transactions with SOF_POS/EOF_POS signals)
                        else (s_payload_len(r) + 3) when INTEL_DEVICE and s_rx_mvb_type_reg(r)='0'                               -- 96-bit header
                        else (s_payload_len(r) + 4);                                                                             -- 128-bit header
   end generate;

   rx_mvb_arr_g : for i in 0 to MVB_ITEMS-1 generate
      s_rx_mvb_data_plus_arr(i) <= s_rx_mvb_data_arr(i) & s_rx_mvb_be_arr_fixed(i) & s_rx_mvb_payload_reg(i) & std_logic_vector(s_total_len(i)) & s_rx_mvb_type_reg(i);
      s_rx_mvb_vld(i) <= s_rx_mvb_vld_reg(i) and s_rx_mvb_src_rdy_reg;
   end generate;

   s_rx_mvb_data_plus <= slv_array_ser(s_rx_mvb_data_plus_arr,MVB_ITEMS,MVB_ITEM_PLUS_WIDTH);

   mvb_shakedown_i : entity work.MVB_SHAKEDOWN
   generic map(
      RX_ITEMS    => MVB_ITEMS,
      TX_ITEMS    => MFB_REGIONS,
      ITEM_WIDTH  => MVB_ITEM_PLUS_WIDTH,
      SHAKE_PORTS => 2
   )
   port map(
      CLK        => CLK,
      RESET      => RESET,

      RX_DATA    => s_rx_mvb_data_plus,
      RX_VLD     => s_rx_mvb_vld_reg,
      RX_SRC_RDY => s_rx_mvb_src_rdy_reg,
      RX_DST_RDY => RX_MVB_DST_RDY,

      TX_DATA    => s_fifo_mvb_data_plus,
      TX_VLD     => s_fifo_mvb_vld,
      TX_NEXT    => s_fifo_mvb_dst_rdy
   );

   s_fifo_mvb_dst_rdy <= s_fifo_mvb_accept and TX_MFB_DST_RDY;
   s_fifo_mvb_data_plus_arr <= slv_array_downto_deser(s_fifo_mvb_data_plus,MFB_REGIONS,MVB_ITEM_PLUS_WIDTH);

   unpack_data_plus_arr_g : for i in 0 to MFB_REGIONS-1 generate
      s_fifo_mvb_data_arr(i)     <= s_fifo_mvb_data_plus_arr(i)(MVB_ITEM_PLUS_WIDTH-1 downto TRANS_SIZE_WIDTH+1+1+8);
      s_fifo_mvb_be(i)           <= s_fifo_mvb_data_plus_arr(i)(TRANS_SIZE_WIDTH+1+1+8-1 downto TRANS_SIZE_WIDTH+1+1);
      s_fifo_mvb_payload(i)      <= s_fifo_mvb_data_plus_arr(i)(TRANS_SIZE_WIDTH+1);
      s_fifo_mvb_payload_size(i) <= s_fifo_mvb_data_plus_arr(i)(TRANS_SIZE_WIDTH+1-1 downto 1);
      s_fifo_mvb_type(i)         <= s_fifo_mvb_data_plus_arr(i)(0);
   end generate;

   -- header multiplexors
   s_hdr_data_muxed_arr(0)     <= s_fifo_mvb_data_arr(0);
   s_hdr_be_muxed(0)           <= s_fifo_mvb_be(0);
   s_hdr_payload_muxed(0)      <= s_fifo_mvb_payload(0);
   s_hdr_payload_size_muxed(0) <= s_fifo_mvb_payload_size(0);
   s_hdr_type_muxed(0)         <= s_fifo_mvb_type(0);
   s_hdr_vld_muxed(0)          <= s_fifo_mvb_vld(0);
   hdr_mux_g : for r in 1 to MFB_REGIONS-1 generate
      s_hdr_data_muxed_arr(r)     <= s_fifo_mvb_data_arr(to_integer(s_hdr_mux_sel(r)));
      s_hdr_be_muxed(r)           <= s_fifo_mvb_be(to_integer(s_hdr_mux_sel(r)));
      s_hdr_payload_muxed(r)      <= s_fifo_mvb_payload(to_integer(s_hdr_mux_sel(r)));
      s_hdr_payload_size_muxed(r) <= s_fifo_mvb_payload_size(to_integer(s_hdr_mux_sel(r)));
      s_hdr_type_muxed(r)         <= s_fifo_mvb_type(to_integer(s_hdr_mux_sel(r)));
      s_hdr_vld_muxed(r)          <= s_fifo_mvb_vld(to_integer(s_hdr_mux_sel(r)));
   end generate;

   mfb_data_arr_g : for r in 0 to MFB_REGIONS-1 generate
      s_mfb_data(r)(MVB_ITEM_WIDTH-1 downto 0) <= s_hdr_data_muxed_arr(r);
      s_mfb_data(r)(MFB_REGION_WIDTH-1 downto MVB_ITEM_WIDTH) <= (others => '0');
   end generate;

   -----------------------------------------------------------------------------
   -- MFB WORD COUNTER
   -----------------------------------------------------------------------------

   s_word_cnt_reg_en <= TX_MFB_DST_RDY and s_mfb_src_rdy;
   s_word_cnt_reg_load <= or s_plan_en;

   word_cnt_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_word_cnt_reg <= (others => '0');
         elsif (s_word_cnt_reg_en = '1') then
            if (s_word_cnt_reg_load = '1') then
                s_word_cnt_reg <= to_unsigned(1,WORD_CNT_W);
            else
                s_word_cnt_reg <= s_word_cnt_reg + 1;
            end if;
         end if;
      end if;
   end process;

   -- word counter per region
   s_word_cnt_per_region(0) <= s_word_cnt_reg;
   word_cnt_per_region_g : for r in 0 to MFB_REGIONS-1 generate
      s_word_cnt_per_region(r+1) <= (others => '0') when (s_plan_en(r) = '1') else s_word_cnt_per_region(r);
   end generate;

   -----------------------------------------------------------------------------
   -- CONTROL LOGIC
   -----------------------------------------------------------------------------

   meta_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_eof_offset(0)   <= (others => '0');
            s_need_set_eof(0) <= '0';
         elsif (TX_MFB_DST_RDY = '1') then
            s_eof_offset(0)   <= s_eof_offset(MFB_REGIONS);
            s_need_set_eof(0) <= s_need_set_eof(MFB_REGIONS);
         end if;
      end if;
   end process;

   -- in first region can be SOF without limitations
   s_plan_wait(0) <= '0';
   -- first header is every time on zero position
   s_hdr_mux_sel(0) <= (others => '0');

   plan_g : for r in 0 to MFB_REGIONS-1 generate
      -- Whole packet is in one region
      s_whole_pkt(r) <= '1' when (unsigned(s_hdr_payload_size_muxed(r)) <= (MFB_REGION_SIZE*MFB_BLOCK_SIZE)) else '0';
      -- create new EOF offset signal from header data
      s_eof_offset_new(r) <= unsigned(s_hdr_payload_size_muxed(r)) + (r*MFB_BLOCK_SIZE) - 1;

      -- create signal with current EOF offset signal
      -- index are shifted by one: index 0 is EOF offset from last region of previous word,
      -- index 1 is EOF offset from first region of current word,...
      s_eof_offset(r+1) <= s_eof_offset_new(r) when (s_plan_en(r) = '1') else s_eof_offset(r);
      s_eof_pos(r) <= s_eof_offset_new(r)(MFB_EOF_POS_WIDTH-1 downto 0) when (s_plan_en(r) = '1') else s_eof_offset(r)(MFB_EOF_POS_WIDTH-1 downto 0);

      -- unpack current EOF offset to word, region and selection part
      s_eof_offset_word(r)   <= s_eof_offset(r)(TRANS_SIZE_WIDTH-1 downto log2(MFB_REGIONS)+MFB_EOF_POS_WIDTH);
      s_eof_offset_region(r) <= s_eof_offset(r)(log2(MFB_REGIONS)+MFB_EOF_POS_WIDTH-1 downto MFB_EOF_POS_WIDTH);

      -- checking if the position matches the EOF offset
      s_eof_word_ok(r)   <= '1' when (s_eof_offset_word(r) = s_word_cnt_per_region(r)) else '0';
      s_eof_region_ok(r) <= '1' when (MFB_REGIONS=1) or (s_eof_offset_region(r) = to_unsigned(r,log2(MFB_REGIONS))) else '0';
      s_eof_ok(r)        <= s_eof_word_ok(r) and s_eof_region_ok(r);
      s_eof_vld(r)       <= (s_eof_ok(r) and s_need_set_eof(r)) or (s_plan_en(r) and s_whole_pkt(r));

      -- planned packet
      s_plan_en(r) <= s_hdr_vld_muxed(r) and not s_need_set_eof(r) and not s_plan_wait(r);
      -- stop planing in next region of current word, first valid data must be
      -- in first byte of the MFB bus word
      -- (logic DEPRECATED - could never be '1', now constant '0')
      --s_plan_wait(r+1) <= '0'; -- not (s_plan_en(r) or s_need_set_eof(r));
      s_plan_wait(r+1) <= '1' when (ONE_PKT_PER_WORD = True) else '0';
      -- select next header only when you accepted previous header
      s_hdr_mux_sel(r+1) <= (s_hdr_mux_sel(r) + 1) when (s_plan_en(r) = '1') else s_hdr_mux_sel(r);
      -- control of creating EOF signal
      s_need_set_eof(r+1) <= '0' when (s_eof_vld(r) = '1') else
                             '1' when (s_plan_en(r) = '1') else s_need_set_eof(r);

      -- some signals of output MFB
      s_mfb_sof(r) <= s_plan_en(r);
      s_mfb_eof(r) <= (s_eof_ok(r) and s_need_set_eof(r)) or (s_plan_en(r) and s_whole_pkt(r));
      s_mfb_eof_pos(r) <= std_logic_vector(s_eof_pos(r));
      s_mfb_be(r) <= s_hdr_be_muxed(r);
      s_mfb_payload(r) <= s_hdr_payload_muxed(r);
      s_mfb_type(r) <= s_hdr_type_muxed(r);
   end generate;

   -- accepted headers in FIFO_MULTI order
   fifo_mvb_accept_p : process (s_plan_en)
      variable var_cnt    : integer range 0 to MFB_REGIONS;
      variable var_accept : std_logic_vector(MFB_REGIONS-1 downto 0);
   begin
      var_accept := (others => '0');
      var_cnt := 0;
      temp_or : for r in 0 to MFB_REGIONS-1 loop
         if (s_plan_en(r) = '1') then
            var_accept(var_cnt) := '1';
            var_cnt := var_cnt + 1;
         end if;
      end loop;
      s_fifo_mvb_accept <= var_accept;
   end process;

   -- create valid (source ready) of output MFB
   s_mfb_src_rdy <= (or s_mfb_sof) or s_need_set_eof(0);

   -----------------------------------------------------------------------------
   -- OUTPUT REGISTERS
   -----------------------------------------------------------------------------

   tx_mfb_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (TX_MFB_DST_RDY = '1') then
            s_tx_mfb_data    <= slv_array_ser(s_mfb_data,MFB_REGIONS,MFB_REGION_WIDTH);
            s_tx_mfb_sof_pos <= (others => '0');
            s_tx_mfb_eof_pos <= slv_array_ser(s_mfb_eof_pos,MFB_REGIONS,MFB_EOF_POS_WIDTH);
            s_tx_mfb_sof     <= s_mfb_sof;
            s_tx_mfb_eof     <= s_mfb_eof;
            s_tx_mfb_be      <= slv_array_ser(s_mfb_be,MFB_REGIONS,8);
            s_tx_mfb_payload <= s_mfb_payload;
            s_tx_mfb_type    <= s_mfb_type;
         end if;
      end if;
   end process;

   tx_mfb_vld_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_tx_mfb_src_rdy <= '0';
         elsif (TX_MFB_DST_RDY = '1') then
            s_tx_mfb_src_rdy <= s_mfb_src_rdy;
         end if;
      end if;
   end process;

   tx_mfb_reg2_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (TX_MFB_DST_RDY = '1') then
            TX_MFB_DATA    <= s_tx_mfb_data;
            TX_MFB_SOF_POS <= s_tx_mfb_sof_pos;
            TX_MFB_EOF_POS <= s_tx_mfb_eof_pos;
            TX_MFB_SOF     <= s_tx_mfb_sof;
            TX_MFB_EOF     <= s_tx_mfb_eof;
            TX_MFB_BE      <= s_tx_mfb_be;
            TX_MFB_PAYLOAD <= s_tx_mfb_payload;
            TX_MFB_TYPE    <= s_tx_mfb_type;
         end if;
      end if;
   end process;

   tx_mfb_vld_reg2_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            TX_MFB_SRC_RDY <= '0';
         elsif (TX_MFB_DST_RDY = '1') then
            TX_MFB_SRC_RDY <= s_tx_mfb_src_rdy;
         end if;
      end if;
   end process;

   -----------------------------------------------------------------------------
   -- MVB OUTPUT (only relevant when PTILE_RTILE_DEVICE)
   -----------------------------------------------------------------------------
   -- MFB_SOF and MFB_SRC_RDY is being propagated even for transactions with no data.
   -- Both SOF_POS and EOF_POS are 0 in that case (transaction with length 1 item).
   -- This might not be correct, but the Intel P_TILE documentation is ambiguous in this point.

   tx_mvb_gen : for i in 0 to MFB_REGIONS-1 generate
      TX_MVB_DATA((i+1)*MVB_ITEM_WIDTH-1 downto i*MVB_ITEM_WIDTH) <= TX_MFB_DATA(i*MFB_REGION_WIDTH+MVB_ITEM_WIDTH-1 downto i*MFB_REGION_WIDTH);
   end generate;
   TX_MVB_VLD <= TX_MFB_SOF;

end architecture;
