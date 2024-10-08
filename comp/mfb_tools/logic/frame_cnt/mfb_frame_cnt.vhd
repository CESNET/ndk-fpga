-- mfb_frame_cnt.vhd: MFB frame counter
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity MFB_FRAME_CNT is
   generic(
      -- MFB configuration
      REGIONS         : natural := 1;
      REGION_SIZE     : natural := 8;
      BLOCK_SIZE      : natural := 8;
      ITEM_WIDTH      : natural := 8;
      OUTPUT_REG      : boolean := true;
      -- Counter configuration
      CNT_WIDTH       : natural := 64;
      AUTO_RESET      : boolean := true;
      IMPLEMENTATION  : string  := "serial" -- "serial", "parallel"
   );
      port(
      -- CLOCK AND RESET
      CLK           : in  std_logic;
      RST           : in  std_logic;
      -- RX MFB INTERFACE
      RX_DATA       : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      RX_SOF_POS    : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      RX_EOF_POS    : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      RX_SOF        : in  std_logic_vector(REGIONS-1 downto 0);
      RX_EOF        : in  std_logic_vector(REGIONS-1 downto 0);
      RX_SRC_RDY    : in  std_logic;
      RX_DST_RDY    : out std_logic;
      -- TX MFB INTERFACE
      TX_DATA       : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      TX_FRAME_NUM  : out std_logic_vector(REGIONS*CNT_WIDTH-1 downto 0); -- valid with SOF
      TX_SOF_POS    : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      TX_EOF_POS    : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      TX_SOF        : out std_logic_vector(REGIONS-1 downto 0);
      TX_EOF        : out std_logic_vector(REGIONS-1 downto 0);
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in  std_logic;
      -- TOTAL FRAME COUNTER
      FRAME_CNT     : out std_logic_vector(CNT_WIDTH-1 downto 0);
      FRAME_CNT_RST : in  std_logic
   );
end MFB_FRAME_CNT;

architecture FULL of MFB_FRAME_CNT is

   type frame_cnt_array_t is array (REGIONS-1 downto 0) of unsigned(CNT_WIDTH-1 downto 0);

   signal frame_cnt_comb     : unsigned(CNT_WIDTH-1 downto 0);
   signal frame_cnt_comb_arr : frame_cnt_array_t;
   signal frame_cnt_reg      : unsigned(CNT_WIDTH-1 downto 0);
   signal frame_cnt_reg_max  : std_logic;
   signal frame_cnt_reg_rst  : std_logic;
   signal frame_cnt_reg_en   : std_logic;
   signal frame_num          : std_logic_vector(REGIONS*CNT_WIDTH-1 downto 0);

begin

   RX_DST_RDY <= TX_DST_RDY;

   -- --------------------------------------------------------------------------
   --  ADDER LOGIC
   -- --------------------------------------------------------------------------

   serial_gen : if IMPLEMENTATION = "serial" generate
      frame_cnt_comb_arr(0) <= frame_cnt_reg + RX_SOF(0);
      adder_logic_serial_g : for r in 1 to REGIONS-1 generate
         adder_logic_serial_p : process (RX_SOF, frame_cnt_comb_arr)
         begin
            frame_cnt_comb_arr(r) <= frame_cnt_comb_arr(r-1) + RX_SOF(r);
         end process;
      end generate;
      frame_cnt_comb <= frame_cnt_comb_arr(REGIONS-1);
   end generate;

   parallel_gen : if IMPLEMENTATION = "parallel" generate
      adder_logic_parallel_g : for r in 0 to REGIONS-1 generate
         adder_logic_parallel_p : process (RX_SOF, frame_cnt_reg)
            variable cnt_var : unsigned(max(1,log2(REGIONS+1))-1 downto 0);
         begin
            cnt_var := (others => '0');
            for i in 0 to r loop
               cnt_var := cnt_var + RX_SOF(i);
            end loop;
            frame_cnt_comb_arr(r) <= cnt_var + frame_cnt_reg;
         end process;
      end generate;
      frame_cnt_comb <= frame_cnt_comb_arr(REGIONS-1);
   end generate;

   -- --------------------------------------------------------------------------
   --  COUNTER REGISTER
   -- --------------------------------------------------------------------------

   frame_cnt_reg_max <= and frame_cnt_reg;
   frame_cnt_reg_rst <= RST or FRAME_CNT_RST;

   auto_reset_on_g : if AUTO_RESET = True generate
      frame_cnt_reg_en <= RX_SRC_RDY and TX_DST_RDY;
   end generate;

   auto_reset_off_g : if AUTO_RESET = False generate
      frame_cnt_reg_en <= (RX_SRC_RDY and TX_DST_RDY) and not frame_cnt_reg_max;
   end generate;

   frame_cnt_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (frame_cnt_reg_rst = '1') then
            frame_cnt_reg <= (others => '0');
         elsif (frame_cnt_reg_en = '1') then
            frame_cnt_reg <= frame_cnt_comb;
         end if;
      end if;
   end process;

   FRAME_CNT <= std_logic_vector(frame_cnt_reg);

   -- --------------------------------------------------------------------------
   --  OUTPUTS ASSIGNMENT
   -- --------------------------------------------------------------------------

   frame_num_g : for r in 0 to REGIONS-1 generate
      frame_num((r+1)*CNT_WIDTH-1 downto r*CNT_WIDTH) <= std_logic_vector(frame_cnt_comb_arr(r));
   end generate;

   out_reg_g : if OUTPUT_REG = True generate
      tx_mfb_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1') then
               TX_DATA      <= RX_DATA;
               TX_FRAME_NUM <= frame_num;
               TX_SOF_POS   <= RX_SOF_POS;
               TX_EOF_POS   <= RX_EOF_POS;
               TX_SOF       <= RX_SOF;
               TX_EOF       <= RX_EOF;
            end if;
         end if;
      end process;

      tx_mfb_vld_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RST = '1') then
               TX_SRC_RDY <= '0';
            elsif (TX_DST_RDY = '1') then
               TX_SRC_RDY <= RX_SRC_RDY;
            end if;
         end if;
      end process;
   end generate;

   no_out_reg_g : if OUTPUT_REG = False generate
      TX_DATA      <= RX_DATA;
      TX_FRAME_NUM <= frame_num;
      TX_SOF_POS   <= RX_SOF_POS;
      TX_EOF_POS   <= RX_EOF_POS;
      TX_SOF       <= RX_SOF;
      TX_EOF       <= RX_EOF;
      TX_SRC_RDY   <= RX_SRC_RDY;
   end generate;

end architecture;
