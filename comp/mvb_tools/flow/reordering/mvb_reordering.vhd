-- mvb_reordering.vhd:
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <xcabal05@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity MVB_REORDERING is
   generic(
      ITEMS         : natural := 5;
      ITEM_WIDTH    : natural := 64;
      OUT_REG_EN    : boolean := True;
      REORDERING_EN : boolean := True
   );
   port(
      CLK         : in  std_logic;
      RESET       : in  std_logic;
      -- MVB RX INTERFACE
      RX_DATA     : in  std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
      RX_VLD      : in  std_logic_vector(ITEMS-1 downto 0);
      RX_SRC_RDY  : in  std_logic;
      RX_DST_RDY  : out std_logic;
      -- MVB TX INTERFACE
      TX_DATA     : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
      TX_VLD      : out std_logic_vector(ITEMS-1 downto 0);
      TX_SRC_RDY  : out std_logic;
      TX_DST_RDY  : in  std_logic;
      -- KEYS FOR REODERING VALID WITH RX_VLD AND RX_SRC_RDY
      REORDER_KEY : in  std_logic_vector(ITEMS*log2(ITEMS)-1 downto 0)
   );
end MVB_REORDERING;

architecture FULL of MVB_REORDERING is

   constant KEY_SIZE : natural := log2(ITEMS);

   type data_array_t is array (ITEMS-1 downto 0) of std_logic_vector(ITEM_WIDTH-1 downto 0);
   type sel_array_t  is array (ITEMS-1 downto 0) of std_logic_vector(KEY_SIZE-1 downto 0);

   signal data_arr         : data_array_t;
   signal reorder_data_arr : data_array_t;
   signal reorder_data     : std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
   signal reorder_vld      : std_logic_vector(ITEMS-1 downto 0);
   signal mux_sel          : std_logic_vector(ITEMS*KEY_SIZE-1 downto 0);
   signal mux_sel_arr      : sel_array_t;

begin

   reordering_on_g : if REORDERING_EN = True generate
      mvb_reordering_logic_i : entity work.MVB_REORDERING_LOGIC
      generic map (
         ITEMS => ITEMS
      )
      port map (
         -- INPUT CONTROL SIGNAL
         REORDER_KEY => REORDER_KEY,
         RX_VLD      => RX_VLD,
         -- OUTPUT CONTROL SIGNAL
         MUX_SEL     => mux_sel,
         TX_VLD      => reorder_vld
      );

      mux_sel_arr_g : for i in 0 to ITEMS-1 generate
         mux_sel_arr(i) <= mux_sel((i+1)*KEY_SIZE-1 downto i*KEY_SIZE);
      end generate;

      mux_g : for i in 0 to ITEMS-1 generate
         gen_mux_i : entity work.GEN_MUX
         generic map (
            DATA_WIDTH => ITEM_WIDTH,
            MUX_WIDTH  => ITEMS
         )
         port map (
            DATA_IN  => RX_DATA,
            SEL      => mux_sel_arr(i),
            DATA_OUT => reorder_data_arr(i)
         );
      end generate;

      tx_data_g : for i in 0 to ITEMS-1 generate
         reorder_data((i+1)*ITEM_WIDTH-1 downto i*ITEM_WIDTH) <= reorder_data_arr(i);
      end generate;
   end generate;

   reordering_off_g : if REORDERING_EN = False generate
      reorder_data <= RX_DATA;
      reorder_vld  <= RX_VLD;
   end generate;

   RX_DST_RDY <= TX_DST_RDY;

   out_reg_on_g : if OUT_REG_EN = True generate
      tx_data_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1') then
               TX_DATA <= reorder_data;
            end if;
         end if;
      end process;

      tx_ctrl_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RESET = '1') then
               TX_SRC_RDY <= '0';
               TX_VLD     <= (others => '0');
            elsif (TX_DST_RDY = '1') then
               TX_SRC_RDY <= RX_SRC_RDY;
               TX_VLD     <= reorder_vld;
            end if;
         end if;
      end process;
   end generate;

   out_reg_off_g : if OUT_REG_EN = False generate
      TX_DATA    <= reorder_data;
      TX_SRC_RDY <= RX_SRC_RDY;
      TX_VLD     <= reorder_vld;
   end generate;

end architecture;
