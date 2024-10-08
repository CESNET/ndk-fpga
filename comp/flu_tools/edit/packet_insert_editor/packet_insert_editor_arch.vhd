--
-- Copyright (C) 2015 CESNET
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
use work.editor_func.all;

-- ----------------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION                            --
-- ----------------------------------------------------------------------------

architecture full of PACKET_INSERT_EDITOR is
   constant pipe_width        : integer := 1 + (8*4) + 4 + OFFSET_WIDTH;

   signal insert_OFFSET       : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal insert_EN_REPLACE   : std_logic;
   signal insert_NEW_DATA     : std_logic_vector(8*4-1 downto 0);
   signal insert_MASK         : std_logic_vector(3 downto 0);
   signal insert_DATA         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal insert_SOP_POS      : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal insert_EOP_POS      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal insert_SOP          : std_logic;
   signal insert_EOP          : std_logic;
   signal insert_SRC_RDY      : std_logic;
   signal insert_DST_RDY      : std_logic;

   signal pipe_OFFSET         : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal pipe_EN_REPLACE     : std_logic;
   signal pipe_NEW_DATA       : std_logic_vector(8*4-1 downto 0);
   signal pipe_MASK           : std_logic_vector(3 downto 0);
   signal pipe_DATA           : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal pipe_SOP_POS        : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal pipe_EOP_POS        : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal pipe_SOP            : std_logic;
   signal pipe_EOP            : std_logic;
   signal pipe_SRC_RDY        : std_logic;
   signal pipe_DST_RDY        : std_logic;

   signal editor_MASK         : std_logic_vector(3 downto 0);
   signal editor_DATA         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal editor_SOP_POS      : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal editor_EOP_POS      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal editor_SOP          : std_logic;
   signal editor_EOP          : std_logic;
   signal editor_SRC_RDY      : std_logic;

   signal pipe_IN             : std_logic_vector(pipe_width-1 downto 0);
   signal pipe_OUT            : std_logic_vector(pipe_width-1 downto 0);
begin

   PACKET_INSERT : entity work.PACKET_INSERT
   generic map(
      DATA_WIDTH 	   => DATA_WIDTH,
      SOP_POS_WIDTH 	=> SOP_POS_WIDTH,
      OFFSET_WIDTH   => OFFSET_WIDTH,
      FAKE_PIPE      => true
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      RX_INSERT_ENABLE  => EN_INSERT,

      RX_EDIT_ENABLE => EN_REPLACE,
      RX_NEW_DATA    => NEW_DATA,
      RX_MASK        => MASK,
      RX_OFFSET      => OFFSET,

      RX_DATA        => RX_DATA,
      RX_SOP_POS     => RX_SOP_POS,
      RX_EOP_POS     => RX_EOP_POS,
      RX_SOP         => RX_SOP,
      RX_EOP         => RX_EOP,
      RX_SRC_RDY     => RX_SRC_RDY,
      RX_DST_RDY     => RX_DST_RDY,

      TX_EDIT_ENABLE => insert_EN_REPLACE,
      TX_NEW_DATA    => insert_NEW_DATA,
      TX_MASK        => insert_MASK,
      TX_OFFSET      => insert_OFFSET,

      TX_DATA        => insert_DATA,
      TX_SOP_POS     => insert_SOP_POS,
      TX_EOP_POS     => insert_EOP_POS,
      TX_SOP         => insert_SOP,
      TX_EOP         => insert_EOP,
      TX_SRC_RDY     => insert_SRC_RDY,
      TX_DST_RDY     => insert_DST_RDY
   );

   pipe_IN <= insert_EN_REPLACE & insert_NEW_DATA & insert_OFFSET & insert_MASK;
   PIPE_inst : entity work.PIPE
   generic map(
      DATA_WIDTH     => pipe_width,
      FAKE_PIPE      => false,
      USE_OUTREG     => true,
      RESET_BY_INIT  => false
   )
   port map(
      CLK           => CLK,
      RESET         => RESET,

      IN_DATA       => pipe_IN,
      IN_SRC_RDY    => insert_SRC_RDY,
      IN_DST_RDY    => open,

      OUT_DATA      => pipe_OUT,
      OUT_SRC_RDY   => open,
      OUT_DST_RDY   => pipe_DST_RDY
   );
   pipe_MASK         <= pipe_OUT(4-1 downto 0);
   pipe_OFFSET       <= pipe_OUT(OFFSET_WIDTH+4-1 downto 4);
   pipe_NEW_DATA     <= pipe_OUT(OFFSET_WIDTH+4+(8*4)-1 downto OFFSET_WIDTH+4);
   pipe_EN_REPLACE   <= pipe_OUT(pipe_width-1);


   FLU_PIPE_inst :entity work.FLU_PIPE
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      FAKE_PIPE      => false,
      USE_OUTREG     => true,
      RESET_BY_INIT  => false
   )
   port map(
      CLK           => CLK,
      RESET         => RESET,

      RX_DATA       => insert_DATA,
      RX_SOP_POS    => insert_SOP_POS,
      RX_EOP_POS    => insert_EOP_POS,
      RX_SOP        => insert_SOP,
      RX_EOP        => insert_EOP,
      RX_SRC_RDY    => insert_SRC_RDY,
      RX_DST_RDY    => insert_DST_RDY,

      TX_DATA       => pipe_DATA,
      TX_SOP_POS    => pipe_SOP_POS,
      TX_EOP_POS    => pipe_EOP_POS,
      TX_SOP        => pipe_SOP,
      TX_EOP        => pipe_EOP,
      TX_SRC_RDY    => pipe_SRC_RDY,
      TX_DST_RDY    => pipe_DST_RDY
   );


   PACKET_EDITOR : entity work.PACKET_EDITOR
   generic map (
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      OFFSET_WIDTH   => OFFSET_WIDTH,
      EN_MASK        => EN_MASK
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,
      NEW_DATA       => pipe_NEW_DATA,
      OFFSET         => pipe_OFFSET,
      EN_REPLACE     => pipe_EN_REPLACE,
      SHIFT          => '0',
      MASK           => pipe_MASK,
      RX_DATA        => pipe_DATA,
      RX_SOP_POS     => pipe_SOP_POS,
      RX_EOP_POS     => pipe_EOP_POS,
      RX_SOP         => pipe_SOP,
      RX_EOP         => pipe_EOP,
      RX_SRC_RDY     => pipe_SRC_RDY,
      RX_DST_RDY     => pipe_DST_RDY,
      TX_DATA        => TX_DATA,
      TX_SOP_POS     => TX_SOP_POS,
      TX_EOP_POS     => TX_EOP_POS,
      TX_SOP         => TX_SOP,
      TX_EOP         => TX_EOP,
      TX_SRC_RDY     => TX_SRC_RDY,
      TX_DST_RDY     => TX_DST_RDY
   );

end architecture;
