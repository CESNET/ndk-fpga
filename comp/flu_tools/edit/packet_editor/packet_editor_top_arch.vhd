-- packet_editor_arch.vhd: architecture of packet editor
-- Copyright (C) 2016 CESNET
-- Author(s): Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION                            --
-- ----------------------------------------------------------------------------

architecture full of PACKET_EDITOR is
   constant offset_width_real : integer := OFFSET_WIDTH + 1;
   signal offset_real         : std_logic_vector(offset_width_real-1 downto 0);
begin

   offset_real(offset_width_real-1) <= '0';
   offset_real(offset_width_real-2 downto 0) <= OFFSET;

   EDITOR_L_inst: entity work.PACKET_EDITOR_L
   generic map(
      DATA_WIDTH 	   => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      OFFSET_WIDTH   => offset_width_real,
      EN_MASK        => EN_MASK
   )
   port map(
      CLK        => CLK,
      RESET      => RESET,
      NEW_DATA   => NEW_DATA,
      SHIFT      => SHIFT,
      MASK       => MASK,
      OFFSET     => offset_real,
      EN_REPLACE => EN_REPLACE,
      RX_DATA    => RX_DATA,
      RX_SOP_POS => RX_SOP_POS,
      RX_EOP_POS => RX_EOP_POS,
      RX_SOP     => RX_SOP,
      RX_EOP     => RX_EOP,
      RX_SRC_RDY => RX_SRC_RDY,
      RX_DST_RDY => RX_DST_RDY,
      TX_DATA    => TX_DATA,
      TX_SOP_POS => TX_SOP_POS,
      TX_EOP_POS => TX_EOP_POS,
      TX_SOP     => TX_SOP,
      TX_EOP     => TX_EOP,
      TX_SRC_RDY => TX_SRC_RDY,
      TX_DST_RDY => TX_DST_RDY
   );
end architecture;
