-- mfb_dropper.vhd: Dropping packets (drop instruction is valid with SOF)
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

-- This component is able to drop the incoming packet when `RX_DROP` input is set to one. This input
-- allows to specify the dropping for each MFB region separately.
entity MFB_DROPPER is
   generic(
      REGIONS     : natural := 4; -- any positive
      REGION_SIZE : natural := 8; -- any power of two
      BLOCK_SIZE  : natural := 8; -- any power of two
      ITEM_WIDTH  : natural := 8; -- any power of two
      META_WIDTH  : natural := 2
   );
   port(
      -- =======================================================================
      -- CLOCK AND RESET
      -- =======================================================================
      CLK        : in  std_logic;
      RESET      : in  std_logic;
      -- =======================================================================
      -- INPUT MFB INTERFACE WITH DROP ENABLE FLAGS
      -- =======================================================================
      RX_DATA    : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      RX_META    : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0) := (others => '0');
      RX_SOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      RX_EOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      RX_SOF     : in  std_logic_vector(REGIONS-1 downto 0);
      RX_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
      RX_SRC_RDY : in  std_logic;
      RX_DST_RDY : out std_logic;
      -- Packet drop, valid with each SOF.
      RX_DROP    : in  std_logic_vector(REGIONS-1 downto 0);
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
      TX_DST_RDY : in  std_logic
   );
end MFB_DROPPER;

architecture FULL of MFB_DROPPER is

   constant SOF_POS_WIDTH : natural := max(1,log2(REGION_SIZE));
   constant EOF_POS_WIDTH : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));

   signal s_rx_sof_pos     : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
   signal s_rx_eof_pos     : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
   signal s_rx_eof_pos_blk : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);

   signal s_sof_before_eof : std_logic_vector(REGIONS-1 downto 0);
   signal s_whole_packet   : std_logic_vector(REGIONS-1 downto 0);
   signal s_drop_lv        : std_logic_vector(REGIONS+1-1 downto 0);

   signal s_sof            : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_curr       : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_prev       : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof            : std_logic_vector(REGIONS-1 downto 0);

   signal s_inc_pkt        : std_logic_vector(REGIONS+1-1 downto 0);
   signal s_region_vld     : std_logic_vector(REGIONS-1 downto 0);
   signal s_src_rdy        : std_logic;

begin

   RX_DST_RDY <= TX_DST_RDY;

   s_rx_sof_pos <= slv_array_downto_deser(RX_SOF_POS,REGIONS,SOF_POS_WIDTH);
   s_rx_eof_pos <= slv_array_downto_deser(RX_EOF_POS,REGIONS,EOF_POS_WIDTH);

   -----------------------------------------------------------------------------
   -- SOF AND EOF MASKING
   -----------------------------------------------------------------------------

   drop_g : for r in 0 to REGIONS-1 generate
      sof_before_eof_g: if (REGION_SIZE > 1) generate
         -- EOF block position
         s_rx_eof_pos_blk(r) <= s_rx_eof_pos(r)(EOF_POS_WIDTH-1 downto log2(BLOCK_SIZE));
         -- SOF is before EOF
         s_sof_before_eof(r) <= '1' when (unsigned(s_rx_sof_pos(r)) <= unsigned(s_rx_eof_pos_blk(r))) else '0';
      else generate
         -- EOF block position
         s_rx_eof_pos_blk(r) <= (others => '0');
         -- SOF is before EOF
         s_sof_before_eof(r) <= '1';
      end generate;

      -- whole packet is in current region
      s_whole_packet(r) <= s_sof_before_eof(r) and RX_SOF(r) and RX_EOF(r);

      -- drop last valid
      s_drop_lv(r+1) <= RX_DROP(r) when (RX_SOF(r) = '1') else s_drop_lv(r);

      -- SOF masking
      s_sof(r) <= RX_SOF(r) and not RX_DROP(r);

      -- EOF masking
      s_eof_curr(r) <= RX_EOF(r) and not RX_DROP(r);
      s_eof_prev(r) <= RX_EOF(r) and not s_drop_lv(r);
      s_eof(r) <= s_eof_curr(r) when (s_whole_packet(r) = '1') else s_eof_prev(r);
   end generate;

   drop_lv_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_drop_lv(0) <= '0';
         elsif (RX_SRC_RDY = '1' and TX_DST_RDY = '1') then
            s_drop_lv(0) <= s_drop_lv(REGIONS);
         end if;
      end if;
   end process;

   -----------------------------------------------------------------------------
   -- SRC_RDY RECALCULATE
   -----------------------------------------------------------------------------

   inc_pkt_g : for r in 0 to REGIONS-1 generate
      s_inc_pkt(r+1) <= (s_sof(r) and not s_eof(r) and not s_inc_pkt(r)) or
                        (s_sof(r) and s_eof(r) and s_inc_pkt(r)) or
                        (not s_sof(r) and not s_eof(r) and s_inc_pkt(r));
   end generate;

   inc_pkt_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_inc_pkt(0) <= '0';
         elsif (RX_SRC_RDY = '1' and TX_DST_RDY = '1') then
            s_inc_pkt(0) <= s_inc_pkt(REGIONS);
         end if;
      end if;
   end process;

   -- calculate valid of regions
   region_vld_g : for r in 0 to REGIONS-1 generate
      s_region_vld(r) <= s_sof(r) or s_inc_pkt(r);
   end generate;

   s_src_rdy <= (or s_region_vld) and RX_SRC_RDY;

   -- --------------------------------------------------------------------------
   --  OUTPUT MFB REGISTERS
   -- --------------------------------------------------------------------------

   tx_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (TX_DST_RDY = '1') then
            TX_DATA    <= RX_DATA;
            TX_META    <= RX_META;
            TX_SOF_POS <= RX_SOF_POS;
            TX_EOF_POS <= RX_EOF_POS;
            TX_SOF     <= s_sof;
            TX_EOF     <= s_eof;
         end if;
      end if;
   end process;

   tx_src_rdy_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            TX_SRC_RDY <= '0';
         elsif (TX_DST_RDY = '1') then
            TX_SRC_RDY <= s_src_rdy;
         end if;
      end if;
   end process;

end architecture;
