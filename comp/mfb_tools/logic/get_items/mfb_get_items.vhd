-- mfb_get_items.vhd: Get item from MFB word
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <xcabal05@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MFB_GET_ITEMS is
   generic(
      -- =======================================================================
      -- MFB DATA BUS CONFIGURATION:
      -- =======================================================================
      REGIONS          : natural := 4; -- any power of two
      REGION_SIZE      : natural := 8; -- any power of two
      BLOCK_SIZE       : natural := 8; -- any power of two
      ITEM_WIDTH       : natural := 8; -- any power of two
      META_WIDTH       : natural := 8;
      -- =======================================================================
      -- OTHER CONFIGURATION:
      -- =======================================================================
      -- Set maximum supported frame lenght in bytes, is used to correctly set
      -- the data width of the word counter.
      MAX_FRAME_LENGHT : natural := 16383;
      -- Count of extracted items.
      -- Minimum value is 1, maximum value is REGION_SIZE*BLOCK_SIZE.
      EXTRACTED_ITEMS  : natural := 4;
      -- Offset of first extracted item from SOF, offset is counted in items.
      -- Minimum value is 0, maximum value is MIN_FRAME_LENGHT-EXTRACTED_ITEMS.
      EXTRACTED_OFFSET : natural := 0
   );
   port(
      -- =======================================================================
      -- CLOCK AND RESET
      -- =======================================================================
      CLK        : in  std_logic;
      RESET      : in  std_logic;
      -- =======================================================================
      -- INPUT MFB INTERFACE
      -- =======================================================================
      RX_DATA    : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      RX_META    : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0) := (others => '0');
      RX_SOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      RX_EOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      RX_SOF     : in  std_logic_vector(REGIONS-1 downto 0);
      RX_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
      RX_SRC_RDY : in  std_logic;
      RX_DST_RDY : out std_logic;
      -- =======================================================================
      -- OUTPUT MFB INTERFACE
      -- =======================================================================
      TX_DATA    : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      TX_META    : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
      TX_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      TX_EOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      TX_SOF     : out std_logic_vector(REGIONS-1 downto 0);
      TX_EOF     : out std_logic_vector(REGIONS-1 downto 0);
      TX_SRC_RDY : out std_logic;
      TX_DST_RDY : in  std_logic;
      -- =======================================================================
      -- OUTPUT MVB INTERFACE WITH EXTRACTED ITEMS
      -- =======================================================================
      EX_DATA    : out std_logic_vector(REGIONS*EXTRACTED_ITEMS*ITEM_WIDTH-1 downto 0);
      EX_VLD     : out std_logic_vector(REGIONS-1 downto 0);
      EX_SRC_RDY : out std_logic := '0';
      EX_DST_RDY : in  std_logic := '1'
   );
end MFB_GET_ITEMS;

architecture FULL of MFB_GET_ITEMS is

   type uns_array_t is array (natural range <>) of unsigned;

   constant DATA_WIDTH          : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
   constant REGION_WIDTH        : natural := REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
   constant REGION_ITEMS        : natural := REGION_SIZE*BLOCK_SIZE;
   constant SOF_POS_WIDTH       : natural := log2(REGION_SIZE);
   constant EOF_POS_WIDTH       : natural := log2(REGION_SIZE*BLOCK_SIZE);
   constant LOG2_REGIONS        : natural := log2(REGIONS);
   constant LOG2_BLOCK_SIZE     : natural := log2(BLOCK_SIZE);
   constant EXTRACTED_WIDTH     : natural := EXTRACTED_ITEMS*ITEM_WIDTH;
   constant WORD_CNT_WIDTH      : natural := log2((MAX_FRAME_LENGHT*8)/DATA_WIDTH)+1;
   constant OFFSET_WIDTH        : natural := WORD_CNT_WIDTH+LOG2_REGIONS+EOF_POS_WIDTH;

   signal s_rx_data_arr         : slv_array_t(REGIONS-1 downto 0)(REGION_WIDTH-1 downto 0);
   signal s_rx_sof_pos_arr      : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
   signal s_rx_sof_vld          : std_logic_vector(REGIONS-1 downto 0);
   signal s_valid_word          : std_logic;

   signal s_word_cnt_reg        : unsigned(WORD_CNT_WIDTH-1 downto 0);
   signal s_word_cnt_per_region : uns_array_t(REGIONS-1 downto 0)(WORD_CNT_WIDTH-1 downto 0);
   signal s_word_cnt_selected   : uns_array_t(REGIONS-1 downto 0)(WORD_CNT_WIDTH-1 downto 0);

   signal s_last_region_reg     : std_logic_vector(REGION_WIDTH-1 downto 0);
   signal s_rx_data_plus_arr    : slv_array_t(REGIONS downto 0)(REGION_WIDTH-1 downto 0);

   signal s_sof_pos_wid         : uns_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
   signal s_sof_offset          : uns_array_t(REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
   signal s_sof_offset_last_vld : uns_array_t(REGIONS downto 0)(OFFSET_WIDTH-1 downto 0);
   signal s_sof_offset_selected : uns_array_t(REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);

   signal s_ex_region_offset    : uns_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH+1 downto 0);
   signal s_ex_over_region      : std_logic_vector(REGIONS-1 downto 0);

   signal s_ex_last_item_offset : uns_array_t(REGIONS-1 downto 0)(OFFSET_WIDTH-1 downto 0);
   signal s_ex_last_item_word   : uns_array_t(REGIONS-1 downto 0)(WORD_CNT_WIDTH-1 downto 0);
   signal s_ex_last_item_region : uns_array_t(REGIONS-1 downto 0)(LOG2_REGIONS-1 downto 0);
   signal s_ex_last_item_sel    : uns_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
   signal s_ex_word_ok          : std_logic_vector(REGIONS-1 downto 0);
   signal s_ex_region_ok        : std_logic_vector(REGIONS-1 downto 0);
   signal s_ex_ok               : std_logic_vector(REGIONS-1 downto 0);

   signal s_ex_done             : std_logic_vector(REGIONS-1 downto 0);
   signal s_ex_done_last_vld    : std_logic_vector(REGIONS downto 0);

   signal s_double_data_arr     : slv_array_t(REGIONS-1 downto 0)(2*REGION_WIDTH-1 downto 0);
   signal s_mux_din_2d_arr      : slv_array_2d_t(REGIONS-1 downto 0)(EXTRACTED_ITEMS-1 downto 0)(REGION_WIDTH-1 downto 0);
   signal s_ex_items_arr        : slv_array_t(REGIONS-1 downto 0)(EXTRACTED_WIDTH-1 downto 0);
   signal s_ex_items_vld        : std_logic_vector(REGIONS-1 downto 0);
   signal s_ex_items            : std_logic_vector(REGIONS*EXTRACTED_WIDTH-1 downto 0);

   signal s_dst_rdy             : std_logic;

begin

   assert (EXTRACTED_ITEMS > 0 and EXTRACTED_ITEMS <= REGION_ITEMS)
      report "Wrong EXTRACTED_ITEMS value! Minimum value is 1, maximum value is REGION_SIZE*BLOCK_SIZE."
      severity failure;

   s_dst_rdy <= TX_DST_RDY and EX_DST_RDY;

   s_rx_data_arr    <= slv_array_downto_deser(RX_DATA,REGIONS,REGION_WIDTH);
   s_rx_sof_pos_arr <= slv_array_downto_deser(RX_SOF_POS,REGIONS,SOF_POS_WIDTH);
   s_rx_sof_vld     <= RX_SOF and RX_SRC_RDY;
   s_valid_word     <= RX_SRC_RDY and s_dst_rdy;

   -----------------------------------------------------------------------------
   -- MFB WORD COUNTER
   -----------------------------------------------------------------------------

   -- word counter register
   word_cnt_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_word_cnt_reg <= (others => '0');
         elsif (s_valid_word = '1') then
            s_word_cnt_reg <= s_word_cnt_per_region(REGIONS-1) + 1;
         end if;
      end if;
   end process;

   -- word counter per region
   s_word_cnt_per_region(0) <= (others => '0') when (s_rx_sof_vld(0) = '1') else s_word_cnt_reg;
   s_word_cnt_selected(0)   <= (others => '0') when (s_rx_sof_vld(0) = '1' and s_ex_over_region(0) = '0') else s_word_cnt_reg;
   word_cnt_per_region_g : for r in 1 to REGIONS-1 generate
      s_word_cnt_per_region(r) <= (others => '0') when (s_rx_sof_vld(r) = '1') else s_word_cnt_per_region(r-1);
      s_word_cnt_selected(r)   <= (others => '0') when (s_rx_sof_vld(r) = '1' and s_ex_over_region(r) = '0') else s_word_cnt_per_region(r-1);
   end generate;

   -- --------------------------------------------------------------------------
   --  LAST REGION REGISTER AND DATA PLUS ARRAY
   -- --------------------------------------------------------------------------

   last_region_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (s_valid_word = '1') then
            s_last_region_reg <= s_rx_data_arr(REGIONS-1);
         end if;
      end if;
   end process;

   s_rx_data_plus_arr(0) <= s_last_region_reg;
   rx_data_plus_arr_g : for r in 0 to REGIONS-1 generate
      s_rx_data_plus_arr(r+1) <= s_rx_data_arr(r);
   end generate;

   -- --------------------------------------------------------------------------
   --  OFFSET LOGIC
   -- --------------------------------------------------------------------------

   sof_offset_last_vld_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (s_dst_rdy='1') then
            s_sof_offset_last_vld(0) <= s_sof_offset_last_vld(REGIONS);
         end if;
      end if;
   end process;

   offset_g : for r in 0 to REGIONS-1 generate
      -- create offset of packet, is counted from begin of word
      s_sof_pos_wid(r)           <= unsigned(s_rx_sof_pos_arr(r)) & to_unsigned(0,LOG2_BLOCK_SIZE);
      s_sof_offset(r)            <= resize((to_unsigned(r,LOG2_REGIONS) & s_sof_pos_wid(r)),OFFSET_WIDTH);
      s_sof_offset_last_vld(r+1) <= s_sof_offset(r) when (s_rx_sof_vld(r) = '1') else s_sof_offset_last_vld(r);
      s_sof_offset_selected(r)   <= s_sof_offset(r) when (s_rx_sof_vld(r) = '1' and s_ex_over_region(r) = '0') else s_sof_offset_last_vld(r);

      -- region offset of last extracted item, is counted from begin of region
      s_ex_region_offset(r) <= s_sof_pos_wid(r) + to_unsigned((EXTRACTED_OFFSET+EXTRACTED_ITEMS-1),EOF_POS_WIDTH+2);

      -- flag of extraction over current region for correctly selected offset and word count
      ex_no_over_region_g : if (REGION_SIZE = 1) generate
         s_ex_over_region(r) <= '0';
      end generate;
      ex_over_region_g : if (REGION_SIZE > 1) generate
         s_ex_over_region(r) <= '1' when (s_ex_region_offset(r) > (REGION_ITEMS-1)) else '0';
      end generate;

      -- create offset of last extracted item
      s_ex_last_item_offset(r) <= s_sof_offset_selected(r) + (EXTRACTED_OFFSET + EXTRACTED_ITEMS - 1);

      -- unpack the last extracted item offset
      s_ex_last_item_word(r)   <= s_ex_last_item_offset(r)(OFFSET_WIDTH-1 downto LOG2_REGIONS+EOF_POS_WIDTH);
      s_ex_last_item_region(r) <= s_ex_last_item_offset(r)(LOG2_REGIONS+EOF_POS_WIDTH-1 downto EOF_POS_WIDTH);
      s_ex_last_item_sel(r)    <= s_ex_last_item_offset(r)(EOF_POS_WIDTH-1 downto 0);

      -- checking if the current position matches with the last extracted item offset
      s_ex_word_ok(r) <= '1' when (s_ex_last_item_word(r) = s_word_cnt_selected(r)) else '0';
      ex_region_ok_force_g : if (REGIONS = 1) generate
         s_ex_region_ok(r) <= '1';
      end generate;
      ex_region_ok_g : if (REGIONS > 1) generate
         s_ex_region_ok(r) <= '1' when (s_ex_last_item_region(r) = to_unsigned(r,log2(REGIONS))) else '0';
      end generate;
      s_ex_ok(r) <= s_ex_word_ok(r) and s_ex_region_ok(r) and not s_ex_done(r);

      s_ex_done(r) <= '0' when (s_rx_sof_vld(r) = '1' and s_ex_over_region(r) = '0') else s_ex_done_last_vld(r);

      ex_done_nosregion_g : if (REGION_SIZE = 1) generate -- ex done without shared regions
         s_ex_done_last_vld(r+1) <= '1' when (s_ex_ok(r) = '1') else
                                    '0' when (s_rx_sof_vld(r) = '1') else s_ex_done_last_vld(r);
      end generate;
      ex_done_sregion_g : if (REGION_SIZE > 1) generate -- ex done with shared regions
         s_ex_done_last_vld(r+1) <= '0' when (s_rx_sof_vld(r) = '1' and (s_ex_over_region(r) = '1' or s_ex_ok(r) = '0')) else
                                    '1' when (s_ex_ok(r) = '1') else s_ex_done_last_vld(r);
      end generate;

   end generate;

   ex_done_last_vld_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_ex_done_last_vld(0) <= '0';
         elsif (s_valid_word = '1') then
            s_ex_done_last_vld(0) <= s_ex_done_last_vld(REGIONS);
         end if;
      end if;
   end process;

   -- --------------------------------------------------------------------------
   --  ITEMS MULTIPLEXORS
   -- --------------------------------------------------------------------------

   items_mux_g : for r in 0 to REGIONS-1 generate
      -- create double data array from current and previous data regions
      s_double_data_arr(r) <= s_rx_data_plus_arr(r+1) & s_rx_data_plus_arr(r);

      item_mux_g : for i in 0 to EXTRACTED_ITEMS-1 generate
         -- create input data for each item multiplexor, so multiplexor select signal could be common to all multiplexors
         s_mux_din_2d_arr(r)(i) <= s_double_data_arr(r)((REGION_ITEMS-EXTRACTED_ITEMS+1+i)*ITEM_WIDTH+REGION_WIDTH-1 downto (REGION_ITEMS-EXTRACTED_ITEMS+1+i)*ITEM_WIDTH);

         -- multiplexor per item
         item_mux_i : entity work.GEN_MUX
         generic map(
            DATA_WIDTH => ITEM_WIDTH,
            MUX_WIDTH  => REGION_ITEMS
         )
         port map(
            DATA_IN  => s_mux_din_2d_arr(r)(i),
            SEL      => std_logic_vector(s_ex_last_item_sel(r)),
            DATA_OUT => s_ex_items_arr(r)((i+1)*ITEM_WIDTH-1 downto i*ITEM_WIDTH)
         );
      end generate;

      -- valid signal of extracted items
      s_ex_items_vld(r) <= s_ex_ok(r) and RX_SRC_RDY and s_dst_rdy;
   end generate;

   -- serialization of extracted items from each region
   s_ex_items <= slv_array_ser(s_ex_items_arr,REGIONS,EXTRACTED_WIDTH);

   -- --------------------------------------------------------------------------
   --  OUTPUT MFB SIGNAL ASSIGMENTS
   -- --------------------------------------------------------------------------

   TX_DATA    <= RX_DATA;
   TX_META    <= RX_META;
   TX_SOF_POS <= RX_SOF_POS;
   TX_EOF_POS <= RX_EOF_POS;
   TX_SOF     <= RX_SOF;
   TX_EOF     <= RX_EOF;
   TX_SRC_RDY <= RX_SRC_RDY and EX_DST_RDY;
   RX_DST_RDY <= s_dst_rdy;

   -- --------------------------------------------------------------------------
   --  OUTPUT REGISTERS WITH EXTRACTED ITEMS
   -- --------------------------------------------------------------------------

   ex_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (s_dst_rdy='1') then
            EX_DATA <= s_ex_items;
            EX_VLD  <= s_ex_items_vld;
         end if;
      end if;
   end process;

   ex_src_rdy_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            EX_SRC_RDY <= '0';
         elsif (EX_DST_RDY='1') then
            EX_SRC_RDY <= or s_ex_items_vld;
         end if;
      end if;
   end process;

end architecture;
