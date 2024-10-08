-- ptc_frame_eraser_upto96bits.vhd: Delete all frames up to 96 bits lenght
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

entity PTC_FRAME_ERASER_UPTO96BITS is
   generic(
      -- =======================================================================
      -- MFB DATA BUS CONFIGURATION:
      -- =======================================================================
      -- Supported configuration is only MFB(4,1,4,32) for PCIe on UltraScale+
      REGIONS      : natural := 4;
      REGION_SIZE  : natural := 1;
      BLOCK_SIZE   : natural := 4;
      ITEM_WIDTH   : natural := 32
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
      TX_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      TX_EOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      TX_SOF     : out std_logic_vector(REGIONS-1 downto 0);
      TX_EOF     : out std_logic_vector(REGIONS-1 downto 0);
      TX_SRC_RDY : out std_logic;
      TX_DST_RDY : in  std_logic
   );
end PTC_FRAME_ERASER_UPTO96BITS;

architecture FULL of PTC_FRAME_ERASER_UPTO96BITS is

   constant EOF_POS_WIDTH   : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));

   signal s_rx_eof_pos_arr  : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
   signal s_bad_eof_pos     : std_logic_vector(REGIONS-1 downto 0);
   signal s_frame_for_erase : std_logic_vector(REGIONS-1 downto 0);
   signal s_sof_mask        : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_mask        : std_logic_vector(REGIONS-1 downto 0);
   signal s_sof_masked      : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_masked      : std_logic_vector(REGIONS-1 downto 0);

   signal s_inc_prev_region : std_logic_vector(REGIONS downto 0);
   signal s_is_frame        : std_logic_vector(REGIONS-1 downto 0);
   signal s_src_rdy_mask    : std_logic;
   signal s_src_rdy_masked  : std_logic;

begin

   -- prepare EOF_POS array
   s_rx_eof_pos_arr <= slv_array_downto_deser(RX_EOF_POS,REGIONS,EOF_POS_WIDTH);

   sof_eof_masking_g : for r in 0 to REGIONS-1 generate
      -- EOF_POS is bad when EOF_POS < 3 dwords
      s_bad_eof_pos(r) <= '1' when (unsigned(s_rx_eof_pos_arr(r)) < 3) else '0';
      -- frame is ready for erase when frame lenght is 1 to 3 dwords
      s_frame_for_erase(r) <= s_bad_eof_pos(r) and RX_SOF(r) and RX_EOF(r);
      -- create masks for SOF and EOF
      s_sof_mask(r) <= not s_frame_for_erase(r);
      s_eof_mask(r) <= not s_frame_for_erase(r);
      -- SOF and EOF masking
      s_sof_masked(r) <= RX_SOF(r) and s_sof_mask(r);
      s_eof_masked(r) <= RX_EOF(r) and s_eof_mask(r);
   end generate;

   -- --------------------------------------------------------------------------
   --  COMPUTE WORD VALID MASK AFTER ERASING
   -- --------------------------------------------------------------------------

   inc_prev_region_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_inc_prev_region(0) <= '0';
         elsif (s_src_rdy_masked = '1' and TX_DST_RDY = '1') then
            s_inc_prev_region(0) <= s_inc_prev_region(REGIONS);
         end if;
      end if;
   end process;

   is_frame_g : for r in 0 to REGIONS-1 generate
      -- compute incomplete frame in this region
      s_inc_prev_region(r+1) <= (s_sof_masked(r) and not s_eof_masked(r) and not s_inc_prev_region(r)) or
                                (not s_sof_masked(r) and not s_eof_masked(r) and s_inc_prev_region(r));
      -- flag of "is frame in this region"
      s_is_frame(r) <= s_sof_masked(r) or s_eof_masked(r) or s_inc_prev_region(r);
   end generate;

   s_src_rdy_mask <= or s_is_frame;
   s_src_rdy_masked <= RX_SRC_RDY and s_src_rdy_mask;

   -- --------------------------------------------------------------------------
   --  MFB SIGNALS
   -- --------------------------------------------------------------------------

   TX_DATA    <= RX_DATA;
   TX_SOF_POS <= RX_SOF_POS;
   TX_EOF_POS <= RX_EOF_POS;
   TX_SOF     <= s_sof_masked;
   TX_EOF     <= s_eof_masked;
   TX_SRC_RDY <= s_src_rdy_masked;
   RX_DST_RDY <= TX_DST_RDY;

end architecture;
