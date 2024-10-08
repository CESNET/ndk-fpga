-- item_trans_ctrl.vhd: Multi-Value Bus item N to M transformer
-- Copyright (C) 2016 CESNET z. s. p. o.
-- Author(s): Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;

entity MVB_ITEM_TRANS_CTRL is
   generic(
      ITEMS_IN       : integer := 1; -- any possitive value
      ITEMS_OUT      : integer := 32; -- any possitive value
      ITEM_WIDTH     : integer := 8; -- any possitive value
      USE_DST_RDY    : boolean := false
   );
   port(
      RX_DATA        : in  std_logic_vector(ITEMS_IN*ITEM_WIDTH-1 downto 0);
      RX_VLD         : in  std_logic_vector(ITEMS_IN-1 downto 0);
      RX_CTRL        : in  std_logic_vector(ITEMS_IN*log2(ITEMS_OUT)-1 downto 0);
      RX_SRC_RDY     : in  std_logic;
      RX_DST_RDY     : out std_logic;

      TX_DATA        : out std_logic_vector(ITEMS_OUT*ITEM_WIDTH-1 downto 0);
      TX_VLD         : out std_logic_vector(ITEMS_OUT-1 downto 0);
      TX_SRC_RDY     : out std_logic;
      TX_DST_RDY     : in  std_logic
   );
end entity;



architecture arch of MVB_ITEM_TRANS_CTRL is

   signal cmp_ctrl         : std_logic_vector(ITEMS_IN*ITEMS_OUT-1 downto 0);
   signal cmp_ctrl_reord   : std_logic_vector(ITEMS_IN*ITEMS_OUT-1 downto 0);
   signal dec              : std_logic_vector(ITEMS_IN*ITEMS_OUT-1 downto 0);
   signal dec_reord        : std_logic_vector(ITEMS_IN*ITEMS_OUT-1 downto 0);

begin

   RX_DST_RDY <= '1';

   -- TX_DATA logic ------------------------------------------------------------

   -- Comparator logic ---------------------------------------------------------
   cmp_ctrlg: for i in 0 to ITEMS_IN-1 generate
      cmp_ctrlgg: for j in 0 to ITEMS_OUT-1 generate
         cmp_ctrl(i*ITEMS_OUT+j) <= RX_CTRL((i+1)*log2(ITEMS_OUT)-1 downto i*log2(ITEMS_OUT)) ?= std_logic_vector(to_unsigned(j, log2(ITEMS_OUT))) and
                                    RX_VLD(i);
      end generate;
   end generate;

   cmp_ctrl_reordg: for i in 0 to ITEMS_OUT-1 generate
      cmp_ctrl_reordgg: for j in 0 to ITEMS_IN-1 generate
         cmp_ctrl_reord(i*ITEMS_IN+j) <= cmp_ctrl(j*ITEMS_OUT+i);
      end generate;
   end generate;

   -- Multiplexor logic
   muxg: for i in 0 to ITEMS_OUT-1 generate

      mux_onehoti:  entity work.GEN_MUX_ONEHOT
      generic map (
         DATA_WIDTH => ITEM_WIDTH,
         MUX_WIDTH => ITEMS_IN
      )
      port map (
         DATA_IN => RX_DATA,
         SEL => cmp_ctrl_reord((i+1)*ITEMS_IN-1 downto i*ITEMS_IN),
         DATA_OUT => TX_DATA((i+1)*ITEM_WIDTH-1 downto i*ITEM_WIDTH)
      );

   end generate;

   -- --------------------------------------------------------------------------

   -- TX_VLD logic -------------------------------------------------------------
   decg: for i in 0 to ITEMS_IN-1 generate

      dec1fni: entity work.dec1fn_enable
      generic map (
         ITEMS => ITEMS_OUT
      )
      port map(
         ADDR => RX_CTRL((i+1)*(log2(ITEMS_OUT))-1 downto i*(log2(ITEMS_OUT))),
         ENABLE => RX_VLD(i) and RX_SRC_RDY,
         DO => dec((i+1)*ITEMS_OUT-1 downto i*ITEMS_OUT)
      );

   end generate;

   dec_reordg: for i in 0 to ITEMS_OUT-1 generate
      dec_reordgg:  for j in 0 to ITEMS_IN-1 generate
         dec_reord(i*ITEMS_IN+j) <= dec(j*ITEMS_OUT+i);
      end generate;
   end generate;

   tx_vldg: for i in 0 to ITEMS_OUT-1 generate
      TX_VLD(i) <= or dec_reord((i+1)*ITEMS_IN-1 downto i*ITEMS_IN);
   end generate;

   -- TX_SRC_RDY logic
   TX_SRC_RDY <= or TX_VLD;

   -- --------------------------------------------------------------------------

end architecture;
