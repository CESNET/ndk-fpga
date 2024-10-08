-- mfb_auxiliary_signals.vhd: Generator of auxiliary signals for MFB bus
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

entity MFB_AUXILIARY_SIGNALS is
   generic(
      -- =======================================================================
      -- MFB BUS CONFIGURATION:
      -- =======================================================================
      REGIONS       : natural := 4;
      REGION_SIZE   : natural := 8;
      BLOCK_SIZE    : natural := 8;
      ITEM_WIDTH    : natural := 8;
      META_WIDTH    : natural := 0;
      -- =======================================================================
      -- AUXILIARY SIGNALS CONFIGURATION:
      -- =======================================================================
      REGION_AUX_EN : boolean := True;
      BLOCK_AUX_EN  : boolean := False;
      ITEM_AUX_EN   : boolean := False
   );
   port(
      -- =======================================================================
      -- CLOCK AND RESET
      -- =======================================================================
      CLK              : in  std_logic;
      RESET            : in  std_logic;
      -- =======================================================================
      -- INPUT MFB INTERFACE
      -- =======================================================================
      RX_DATA          : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      RX_META          : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0) := (others => '0');
      RX_SOF_POS       : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      RX_EOF_POS       : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      RX_SOF           : in  std_logic_vector(REGIONS-1 downto 0);
      RX_EOF           : in  std_logic_vector(REGIONS-1 downto 0);
      RX_SRC_RDY       : in  std_logic;
      RX_DST_RDY       : out std_logic;
      -- =======================================================================
      -- OUTPUT MFB INTERFACE
      -- =======================================================================
      TX_DATA          : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      TX_META          : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
      TX_SOF_POS       : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      TX_EOF_POS       : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      TX_SOF           : out std_logic_vector(REGIONS-1 downto 0);
      TX_EOF           : out std_logic_vector(REGIONS-1 downto 0);
      TX_SRC_RDY       : out std_logic;
      TX_DST_RDY       : in  std_logic;
      -- =======================================================================
      -- OUTPUT MFB AUXILIARY SIGNALS
      -- =======================================================================
      -- Array of flags, flag is high when the region shares two frames.
      TX_REGION_SHARED : out std_logic_vector(REGIONS-1 downto 0);
      -- Array of valids for each region in the MFB word.
      TX_REGION_VLD    : out std_logic_vector(REGIONS-1 downto 0);
      -- Array of valids for each block in the MFB word.
      TX_BLOCK_VLD     : out std_logic_vector(REGIONS*REGION_SIZE-1 downto 0);
      -- Array of valids for each item in the MFB word.
      TX_ITEM_VLD      : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE-1 downto 0)
   );
end MFB_AUXILIARY_SIGNALS;

architecture FULL of MFB_AUXILIARY_SIGNALS is

   constant WORD_BLOCKS         : natural := REGIONS*REGION_SIZE;
   constant REGION_BLOCKS       : natural := REGION_SIZE;
   constant WORD_ITEMS          : natural := REGIONS*REGION_SIZE*BLOCK_SIZE;
   constant REGION_ITEMS        : natural := REGION_SIZE*BLOCK_SIZE;
   constant LOG2_REGION_BLOCKS  : natural := log2(REGION_BLOCKS);
   constant LOG2_REGION_ITEMS   : natural := log2(REGION_ITEMS);
   constant LOG2_BLOCK_SIZE     : natural := log2(BLOCK_SIZE);

   signal s_rx_sof_block_arr    : slv_array_t(REGIONS-1 downto 0)(LOG2_REGION_BLOCKS-1 downto 0);
   signal s_rx_eof_block_arr    : slv_array_t(REGIONS-1 downto 0)(LOG2_REGION_BLOCKS-1 downto 0);
   signal s_rx_sof_item_arr     : slv_array_t(REGIONS-1 downto 0)(LOG2_REGION_ITEMS-1 downto 0);
   signal s_rx_eof_item_arr     : slv_array_t(REGIONS-1 downto 0)(LOG2_REGION_ITEMS-1 downto 0);

   signal s_incomplete_region   : std_logic_vector(REGIONS downto 0);
   signal s_region_vld          : std_logic_vector(REGIONS-1 downto 0);
   signal s_region_shared       : std_logic_vector(REGIONS-1 downto 0);

   signal s_rx_sof_block_onehot : std_logic_vector(WORD_BLOCKS-1 downto 0);
   signal s_rx_eof_block_onehot : std_logic_vector(WORD_BLOCKS-1 downto 0);
   signal s_incomplete_block    : std_logic_vector(WORD_BLOCKS downto 0);
   signal s_block_vld           : std_logic_vector(WORD_BLOCKS-1 downto 0);

   signal s_rx_sof_item_onehot  : std_logic_vector(WORD_ITEMS-1 downto 0);
   signal s_rx_eof_item_onehot  : std_logic_vector(WORD_ITEMS-1 downto 0);
   signal s_incomplete_item     : std_logic_vector(WORD_ITEMS downto 0);
   signal s_item_vld            : std_logic_vector(WORD_ITEMS-1 downto 0);

begin

   --  CREATE MFB SOF_POS AND EOF_POS ARRAYS
   item_rx_sof_block_arr_g : if REGION_BLOCKS > 1 generate
      s_rx_sof_block_arr <= slv_array_downto_deser(RX_SOF_POS,REGIONS,LOG2_REGION_BLOCKS);
   else generate
      s_rx_sof_block_arr <= (others => (others => '0'));
   end generate;

   rx_eof_item_arr_g : if REGION_ITEMS > 1 generate
      s_rx_eof_item_arr <= slv_array_downto_deser(RX_EOF_POS,REGIONS,LOG2_REGION_ITEMS);
   else generate
      s_rx_eof_item_arr <= (others => (others => '0'));
   end generate;

   sof_eof_array_g : for r in 0 to REGIONS-1 generate
      s_rx_sof_item_arr(r)  <= s_rx_sof_block_arr(r) & std_logic_vector(to_unsigned(0,LOG2_BLOCK_SIZE));
      s_rx_eof_block_arr(r) <= s_rx_eof_item_arr(r)(LOG2_REGION_ITEMS-1 downto LOG2_BLOCK_SIZE);
   end generate;

   -- --------------------------------------------------------------------------
   --  VALID AND SHARED FOR EACH REGION
   -- --------------------------------------------------------------------------

   region_aux_g : if REGION_AUX_EN generate
      incomplete_region_g : for r in 0 to REGIONS-1 generate
         s_incomplete_region(r+1) <= (RX_SOF(r) and not RX_EOF(r) and not s_incomplete_region(r)) or
            (RX_SOF(r) and RX_EOF(r) and s_incomplete_region(r)) or
            (not RX_SOF(r) and not RX_EOF(r) and s_incomplete_region(r));
      end generate;

      incomplete_region_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RESET = '1') then
               s_incomplete_region(0) <= '0';
            elsif (RX_SRC_RDY = '1' and TX_DST_RDY = '1') then
               s_incomplete_region(0) <= s_incomplete_region(REGIONS);
            end if;
         end if;
      end process;

      region_g : for r in 0 to REGIONS-1 generate
         s_region_vld(r)    <= RX_SOF(r) or RX_EOF(r) or s_incomplete_region(r);
         s_region_shared(r) <= RX_SOF(r) and RX_EOF(r) and s_incomplete_region(r);
      end generate;
   end generate;

   region_aux_off_g : if not REGION_AUX_EN generate
      s_region_vld    <= (others => '0');
      s_region_shared <= (others => '0');
   end generate;

   -- --------------------------------------------------------------------------
   --  VALID FOR EACH BLOCK
   -- --------------------------------------------------------------------------

   block_aux_g : if BLOCK_AUX_EN generate
      block_onehot_g : for r in 0 to REGIONS-1 generate
         sof_block_onehot_i : entity work.BIN2HOT
         generic map(
            DATA_WIDTH => LOG2_REGION_BLOCKS
         )
         port map(
            EN     => RX_SOF(r),
            INPUT  => s_rx_sof_block_arr(r),
            OUTPUT => s_rx_sof_block_onehot((r+1)*REGION_BLOCKS-1 downto r*REGION_BLOCKS)
         );

         eof_block_onehot_i : entity work.BIN2HOT
         generic map(
            DATA_WIDTH => LOG2_REGION_BLOCKS
         )
         port map(
            EN     => RX_EOF(r),
            INPUT  => s_rx_eof_block_arr(r),
            OUTPUT => s_rx_eof_block_onehot((r+1)*REGION_BLOCKS-1 downto r*REGION_BLOCKS)
         );
      end generate;

      incomplete_block_g : for r in 0 to WORD_BLOCKS-1 generate
         incomplete_block_p : process (s_incomplete_block,s_rx_sof_block_onehot,s_rx_eof_block_onehot)
               variable v_inc_blk : std_logic;
         begin
               v_inc_blk := s_incomplete_block(0);
               inc_blk_l : for i in 0 to r loop
                  v_inc_blk := (s_rx_sof_block_onehot(i) or v_inc_blk) and not s_rx_eof_block_onehot(i);
               end loop;
               s_incomplete_block(r+1) <= v_inc_blk;
         end process;
      end generate;

      incomplete_block_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RESET = '1') then
               s_incomplete_block(0) <= '0';
            elsif (RX_SRC_RDY = '1' and TX_DST_RDY = '1') then
               s_incomplete_block(0) <= s_incomplete_block(WORD_BLOCKS);
            end if;
         end if;
      end process;

      block_vld_g : for i in 0 to WORD_BLOCKS-1 generate
         s_block_vld(i) <= s_rx_sof_block_onehot(i) or s_rx_eof_block_onehot(i) or s_incomplete_block(i);
      end generate;
   end generate;

   block_aux_off_g : if not BLOCK_AUX_EN generate
      s_block_vld <= (others => '0');
   end generate;

   -- --------------------------------------------------------------------------
   --  VALID FOR EACH ITEM
   -- --------------------------------------------------------------------------

   item_aux_g : if ITEM_AUX_EN generate
      item_onehot_g : for r in 0 to REGIONS-1 generate
         sof_item_onehot_i : entity work.BIN2HOT
         generic map(
            DATA_WIDTH => LOG2_REGION_ITEMS
         )
         port map(
            EN     => RX_SOF(r),
            INPUT  => s_rx_sof_item_arr(r),
            OUTPUT => s_rx_sof_item_onehot((r+1)*REGION_ITEMS-1 downto r*REGION_ITEMS)
         );

         eof_item_onehot_i : entity work.BIN2HOT
         generic map(
            DATA_WIDTH => LOG2_REGION_ITEMS
         )
         port map(
            EN     => RX_EOF(r),
            INPUT  => s_rx_eof_item_arr(r),
            OUTPUT => s_rx_eof_item_onehot((r+1)*REGION_ITEMS-1 downto r*REGION_ITEMS)
         );
      end generate;

      incomplete_item_g : for r in 0 to WORD_ITEMS-1 generate
         incomplete_item_p : process (s_incomplete_item,s_rx_sof_item_onehot,s_rx_eof_item_onehot)
            variable v_inc_itm : std_logic;
         begin
            v_inc_itm := s_incomplete_item(0);
            inc_blk_l : for i in 0 to r loop
               v_inc_itm := (s_rx_sof_item_onehot(i) or v_inc_itm) and not s_rx_eof_item_onehot(i);
            end loop;
            s_incomplete_item(r+1) <= v_inc_itm;
         end process;
      end generate;

      incomplete_item_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RESET = '1') then
               s_incomplete_item(0) <= '0';
            elsif (RX_SRC_RDY = '1' and TX_DST_RDY = '1') then
               s_incomplete_item(0) <= s_incomplete_item(WORD_ITEMS);
            end if;
         end if;
      end process;

      item_vld_g : for i in 0 to WORD_ITEMS-1 generate
         s_item_vld(i) <= s_rx_sof_item_onehot(i) or s_rx_eof_item_onehot(i) or s_incomplete_item(i);
      end generate;
   end generate;

   item_aux_off_g : if not ITEM_AUX_EN generate
      s_item_vld <= (others => '0');
   end generate;

   -----------------------------------------------------------------------------
   -- TX SIGNALS
   -----------------------------------------------------------------------------

   -- MFB original signals
   TX_DATA    <= RX_DATA;
   TX_META    <= RX_META;
   TX_SOF_POS <= RX_SOF_POS;
   TX_EOF_POS <= RX_EOF_POS;
   TX_SOF     <= RX_SOF;
   TX_EOF     <= RX_EOF;
   TX_SRC_RDY <= RX_SRC_RDY;
   RX_DST_RDY <= TX_DST_RDY;

   -- MFB helper signals
   TX_REGION_SHARED <= s_region_shared;
   TX_REGION_VLD    <= s_region_vld;
   TX_BLOCK_VLD     <= s_block_vld;
   TX_ITEM_VLD      <= s_item_vld;

end architecture;
