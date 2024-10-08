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

architecture full of MAC_EDITOR is
   constant pipe_width        : integer := 6*8 +  6  +   1;
                                         --mac  mask   mac_wr
   signal DST_MAC_DATA        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal DST_MAC_SOP_POS     : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal DST_MAC_EOP_POS     : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal DST_MAC_SOP         : std_logic;
   signal DST_MAC_EOP         : std_logic;
   signal DST_MAC_SRC_RDY     : std_logic;
   signal DST_MAC_DST_RDY     : std_logic;

   signal PIPE_DATA           : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal PIPE_SOP_POS        : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal PIPE_EOP_POS        : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal PIPE_SOP            : std_logic;
   signal PIPE_EOP            : std_logic;
   signal PIPE_SRC_RDY        : std_logic;
   signal PIPE_DST_RDY        : std_logic;
   signal PIPE_SRC_W          : std_logic;
   signal PIPE_SRC_DATA       : std_logic_vector(6*8-1 downto 0);
   signal PIPE_SRC_MASK       : std_logic_vector(6-1 downto 0);

   signal pipe_in_data        : std_logic_vector(pipe_width-1 downto 0);
   signal pipe_out_data       : std_logic_vector(pipe_width-1 downto 0);
begin

   MAC_DST_i : entity work.DST_REPLACE
   generic map (
      DATA_WIDTH 	   => DATA_WIDTH,
      SOP_POS_WIDTH 	=> SOP_POS_WIDTH
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      RX_DATA        => RX_DATA,
      RX_SOP_POS     => RX_SOP_POS,
      RX_EOP_POS     => RX_EOP_POS,
      RX_SOP         => RX_SOP,
      RX_EOP         => RX_EOP,
      RX_SRC_RDY     => RX_SRC_RDY,
      RX_DST_RDY     => RX_DST_RDY,
      TX_DATA        => DST_MAC_DATA,
      TX_SOP_POS     => DST_MAC_SOP_POS,
      TX_EOP_POS     => DST_MAC_EOP_POS,
      TX_SOP         => DST_MAC_SOP,
      TX_EOP         => DST_MAC_EOP,
      TX_SRC_RDY     => DST_MAC_SRC_RDY,
      TX_DST_RDY     => DST_MAC_DST_RDY,
      MAC_W          => DST_W,
      MAC_DATA       => DST_DATA,
      MAC_MASK       => DST_MASK
   );

   PIPE_i : entity work.FLU_PIPE
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      FAKE_PIPE      => FAKE_PIPE
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      RX_DATA        => DST_MAC_DATA,
      RX_SOP_POS     => DST_MAC_SOP_POS,
      RX_EOP_POS     => DST_MAC_EOP_POS,
      RX_SOP         => DST_MAC_SOP,
      RX_EOP         => DST_MAC_EOP,
      RX_SRC_RDY     => DST_MAC_SRC_RDY,
      RX_DST_RDY     => DST_MAC_DST_RDY,
      TX_DATA        => PIPE_DATA,
      TX_SOP_POS     => PIPE_SOP_POS,
      TX_EOP_POS     => PIPE_EOP_POS,
      TX_SOP         => PIPE_SOP,
      TX_EOP         => PIPE_EOP,
      TX_SRC_RDY     => PIPE_SRC_RDY,
      TX_DST_RDY     => PIPE_DST_RDY
   );

   pipe_in_data <= SRC_W & SRC_DATA & SRC_MASK;
   PIPE_DATA_i : entity work.PIPE
   generic map(
      DATA_WIDTH     => pipe_width,
      FAKE_PIPE      => FAKE_PIPE
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      IN_DATA        => pipe_in_data,
      IN_SRC_RDY     => DST_MAC_SRC_RDY,
      IN_DST_RDY     => open,
      OUT_DATA       => pipe_out_data,
      OUT_SRC_RDY    => open,
      OUT_DST_RDY    => PIPE_DST_RDY
   );
   PIPE_SRC_MASK <= pipe_out_data(SRC_MASK'length-1 downto 0);
   PIPE_SRC_DATA <= pipe_out_data(SRC_MASK'length+SRC_DATA'length-1 downto SRC_MASK'length);
   PIPE_SRC_W    <= pipe_out_data(pipe_out_data'length-1);

   MAC_SRC_i : entity work.SRC_REPLACE
   generic map (
      DATA_WIDTH 	   => DATA_WIDTH,
      SOP_POS_WIDTH 	=> SOP_POS_WIDTH
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      RX_DATA        => PIPE_DATA,
      RX_SOP_POS     => PIPE_SOP_POS,
      RX_EOP_POS     => PIPE_EOP_POS,
      RX_SOP         => PIPE_SOP,
      RX_EOP         => PIPE_EOP,
      RX_SRC_RDY     => PIPE_SRC_RDY,
      RX_DST_RDY     => PIPE_DST_RDY,
      TX_DATA        => TX_DATA,
      TX_SOP_POS     => TX_SOP_POS,
      TX_EOP_POS     => TX_EOP_POS,
      TX_SOP         => TX_SOP,
      TX_EOP         => TX_EOP,
      TX_SRC_RDY     => TX_SRC_RDY,
      TX_DST_RDY     => TX_DST_RDY,
      MAC_W          => PIPE_SRC_W,
      MAC_DATA       => PIPE_SRC_DATA,
      MAC_MASK       => PIPE_SRC_MASK
   );
end architecture;
