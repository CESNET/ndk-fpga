-- Copyright (C) 2016 CESNET
-- Author(s): Mário Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

entity PACKET_INSERT_L is
   generic(
      --! data width
      DATA_WIDTH 	   : integer := 512;
      --! sop_pos whidth (max value = log2(DATA_WIDTH/8))
      SOP_POS_WIDTH 	: integer := 3;
      --! offset for insert and edit data in packet
      OFFSET_WIDTH   : integer := 10;
      --! pipe
      FAKE_PIPE      : boolean := true
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- enable insert 4B to packet
      RX_INSERT_ENABLE  : in std_logic;

      -- enable edit 4B in packet
      RX_EDIT_ENABLE : in std_logic;
      RX_NEW_DATA    : in std_logic_vector((4*8)-1 downto 0);
      RX_MASK        : in std_logic_vector(3 downto 0);
      RX_OFFSET      : in std_logic_vector(OFFSET_WIDTH-1 downto 0);
      --! Frame Link Unaligned input interface
      RX_DATA        : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS     : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS     : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP         : in std_logic;
      RX_EOP         : in std_logic;
      RX_SRC_RDY     : in std_logic;
      RX_DST_RDY     : out std_logic;

      TX_EDIT_ENABLE : out std_logic;
      TX_NEW_DATA    : out std_logic_vector((4*8)-1 downto 0);
      TX_MASK        : out std_logic_vector(3 downto 0);
      TX_OFFSET      : out std_logic_vector(OFFSET_WIDTH-1 downto 0);
      --! Frame Link Unaligned output interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS     : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS     : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP         : out std_logic;
      TX_EOP         : out std_logic;
      TX_SRC_RDY     : out std_logic;
      TX_DST_RDY     : in std_logic
   );
end entity;

architecture full of PACKET_INSERT_L is
   constant pipe_width                 : integer := (2*OFFSET_WIDTH)+4+(8*4)+3+3+1;
   -- FLU_SPLIT
   signal flu_split_DATA               : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal flu_split_SOP_POS            : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal flu_split_EOP_POS            : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal flu_split_SOP                : std_logic;
   signal flu_split_EOP                : std_logic;
   signal flu_split_SRC_RDY            : std_logic;
   signal flu_split_DST_RDY            : std_logic;
   signal flu_split_insert_enable      : std_logic;
   signal flu_split_frame_state        : std_logic_vector(2 downto 0);
   signal flu_split_pac_shifting       : std_logic;
   signal flu_split_EDIT_ENABLE        : std_logic;
   signal flu_split_NEW_DATA           : std_logic_vector((4*8)-1 downto 0);
   signal flu_split_MASK               : std_logic_vector(3 downto 0);
   signal flu_split_OFFSET             : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   -- HIGHT_SOP_EOP
   signal high_DATA                    : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal high_SOP_POS                 : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal high_EOP_POS                 : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal high_SOP                     : std_logic;
   signal high_EOP                     : std_logic;
   signal high_SRC_RDY                 : std_logic;
   signal high_DST_RDY                 : std_logic;
   signal high_eop_next_frame          : std_logic;
   signal high_insert_enable           : std_logic;
   signal high_EDIT_ENABLE             : std_logic;
   signal high_NEW_DATA                : std_logic_vector((4*8)-1 downto 0);
   signal high_MASK                    : std_logic_vector(3 downto 0);
   signal high_OFFSET                  : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   -- INSERT_OFFSET
   signal offset_DATA                  : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal offset_SOP_POS               : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal offset_EOP_POS               : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal offset_SOP                   : std_logic;
   signal offset_EOP                   : std_logic;
   signal offset_SRC_RDY               : std_logic;
   signal offset_DST_RDY               : std_logic;
   signal offset_block_insert_offset   : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal offset_insert_begin          : std_logic;
   signal offset_eop_next_frame        : std_logic;
   signal offset_EDIT_ENABLE           : std_logic;
   signal offset_NEW_DATA              : std_logic_vector((4*8)-1 downto 0);
   signal offset_MASK                  : std_logic_vector(3 downto 0);
   signal offset_flu_state             : std_logic_vector(2 downto 0);
   signal offset_OFFSET                : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal offset_insert                : std_logic;
   -- PIPE
   signal pipe_DATA                    : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal pipe_SOP_POS                 : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal pipe_EOP_POS                 : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal pipe_SOP                     : std_logic;
   signal pipe_EOP                     : std_logic;
   signal pipe_SRC_RDY                 : std_logic;
   signal pipe_DST_RDY                 : std_logic;
   signal pipe_block_insert_offset     : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal pipe_insert_begin            : std_logic;
   signal pipe_eop_next_frame          : std_logic;
   signal pipe_EDIT_ENABLE             : std_logic;
   signal pipe_NEW_DATA                : std_logic_vector((4*8)-1 downto 0);
   signal pipe_MASK                    : std_logic_vector(3 downto 0);
   signal pipe_OFFSET                  : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal pipe_IN                      : std_logic_vector(pipe_width-1 downto 0);
   signal pipe_OUT                     : std_logic_vector(pipe_width-1 downto 0);
   signal pipe_flu_state               : std_logic_vector(2 downto 0);
   signal pipe_insert                  : std_logic;
begin

   FLU_SPLIT_inst: entity work.FLU_SPLIT
   generic map(
      DATA_WIDTH        => DATA_WIDTH,
      SOP_POS_WIDTH     => SOP_POS_WIDTH,
      OFFSET_WIDTH      => OFFSET_WIDTH
   )
   port map(
      CLK               => CLK,
      RESET             => RESET,

      RX_INSERT_ENABLE  => RX_INSERT_ENABLE,
      RX_EDIT_ENABLE    => RX_EDIT_ENABLE,
      RX_NEW_DATA       => RX_NEW_DATA,
      RX_MASK           => RX_MASK,
      RX_OFFSET         => RX_OFFSET,
      RX_DATA           => RX_DATA,
      RX_SOP_POS        => RX_SOP_POS,
      RX_EOP_POS        => RX_EOP_POS,
      RX_SOP            => RX_SOP,
      RX_EOP            => RX_EOP,
      RX_SRC_RDY        => RX_SRC_RDY,
      RX_DST_RDY        => RX_DST_RDY,

      FRAME_SATE        => flu_split_frame_state,
      PAC_SHIFTING      => flu_split_pac_shifting,
      TX_INSERT_ENABLE  => flu_split_insert_enable,
      TX_EDIT_ENABLE    => flu_split_EDIT_ENABLE,
      TX_NEW_DATA       => flu_split_NEW_DATA,
      TX_MASK           => flu_split_MASK,
      TX_OFFSET         => flu_split_offset,
      TX_DATA           => flu_split_DATA,
      TX_SOP_POS        => flu_split_SOP_POS ,
      TX_EOP_POS        => flu_split_EOP_POS ,
      TX_SOP            => flu_split_SOP,
      TX_EOP            => flu_split_EOP,
      TX_SRC_RDY        => flu_split_SRC_RDY ,
      TX_DST_RDY        => flu_split_DST_RDY
   );

   HIGH_SOP_EOP_inst: entity work.HIGH_SOP_EOP
   generic map(
      DATA_WIDTH 	      => DATA_WIDTH,
      SOP_POS_WIDTH 	   => SOP_POS_WIDTH,
      OFFSET_WIDTH      => OFFSET_WIDTH
   )
   port map(
      CLK               => CLK,
      RESET             => RESET,

      PAC_SHIFTING      => flu_split_pac_shifting,
      FRAME_SATE        => flu_split_frame_state,
      RX_INSERT_ENABLE  => flu_split_insert_enable,
      RX_EDIT_ENABLE    => flu_split_EDIT_ENABLE,
      RX_NEW_DATA       => flu_split_NEW_DATA,
      RX_MASK           => flu_split_MASK,
      RX_OFFSET         => flu_split_offset,
      RX_DATA           => flu_split_DATA,
      RX_SOP_POS        => flu_split_SOP_POS,
      RX_EOP_POS        => flu_split_EOP_POS,
      RX_SOP            => flu_split_SOP,
      RX_EOP            => flu_split_EOP,
      RX_SRC_RDY        => flu_split_SRC_RDY,
      RX_DST_RDY        => flu_split_DST_RDY,

      TX_INSERT_ENABLE  => high_insert_enable,
      TX_EOP_NEXT_FRAME => high_eop_next_frame,
      TX_EDIT_ENABLE    => high_EDIT_ENABLE,
      TX_NEW_DATA       => high_NEW_DATA,
      TX_MASK           => high_MASK,
      TX_OFFSET         => high_offset,
      TX_DATA           => high_DATA,
      TX_SOP_POS        => high_SOP_POS,
      TX_EOP_POS        => high_EOP_POS,
      TX_SOP            => high_SOP,
      TX_EOP            => high_EOP,
      TX_SRC_RDY        => high_SRC_RDY,
      TX_DST_RDY        => high_DST_RDY
   );

   INSERT_OFFSET_inst: entity work.INSERT_OFFSET
   generic map(
      DATA_WIDTH 	         => DATA_WIDTH,
      SOP_POS_WIDTH 	      => SOP_POS_WIDTH,
      OFFSET_WIDTH         => OFFSET_WIDTH
   )
   port map(
      CLK                  => CLK,
      RESET                => RESET,

      OFFSET               => high_offset,
      EN_INSERT            => high_insert_enable,
      RX_EOP_NEXT_FRAME    => high_eop_next_frame,
      RX_EDIT_ENABLE       => high_EDIT_ENABLE,
      RX_NEW_DATA          => high_NEW_DATA,
      RX_MASK              => high_MASK,
      RX_DATA              => high_DATA,
      RX_SOP_POS           => high_SOP_POS,
      RX_EOP_POS           => high_EOP_POS,
      RX_SOP               => high_SOP,
      RX_EOP               => high_EOP,
      RX_SRC_RDY           => high_SRC_RDY,
      RX_DST_RDY           => high_DST_RDY,

      BLOCK_INSER_OFFSET   => offset_block_insert_offset,
      BLOCK_INSER_BEGIN    => offset_insert_begin,

      TX_EOP_NEXT_FRAME    => offset_eop_next_frame,
      TX_FLU_STATE         => offset_flu_state,
      TX_EDIT_ENABLE       => offset_EDIT_ENABLE,
      TX_NEW_DATA          => offset_NEW_DATA,
      TX_MASK              => offset_MASK,
      TX_OFFSET            => offset_offset,
      TX_DATA              => offset_DATA,
      TX_SOP_POS           => offset_SOP_POS,
      TX_EOP_POS           => offset_EOP_POS,
      TX_SOP               => offset_SOP,
      TX_EOP               => offset_EOP,
      TX_SRC_RDY           => offset_SRC_RDY,
      TX_DST_RDY           => offset_DST_RDY,
      TX_INSERT            => offset_insert
   );

   pipe_IN <= offset_EDIT_ENABLE &
              offset_eop_next_frame &
              offset_insert_begin &
              offset_insert &
              offset_flu_state &
              offset_block_insert_offset &
              offset_NEW_DATA &
              offset_OFFSET &
              offset_MASK;

   -- PIPE
   PIPE_inst : entity work.PIPE
   generic map(
      DATA_WIDTH     => pipe_width,
      FAKE_PIPE      => FAKE_PIPE,
      RESET_BY_INIT  => false,
      USE_OUTREG     => true
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      IN_DATA        => pipe_IN,
      IN_SRC_RDY     => offset_SRC_RDY,
      IN_DST_RDY     => open,

      OUT_DATA       => pipe_OUT,
      OUT_SRC_RDY    => open,
      OUT_DST_RDY    => pipe_DST_RDY
   );
   pipe_MASK                  <= pipe_OUT(4-1 downto 0);
   pipe_OFFSET                <= pipe_OUT(OFFSET_WIDTH+4-1 downto 4);
   pipe_NEW_DATA              <= pipe_OUT(OFFSET_WIDTH+4+(8*4)-1 downto OFFSET_WIDTH+4);
   pipe_block_insert_offset   <= pipe_OUT((2*OFFSET_WIDTH)+4+(8*4)-1 downto OFFSET_WIDTH+4+(8*4));
   pipe_flu_state             <= pipe_OUT((2*OFFSET_WIDTH)+4+(8*4)+3-1 downto (2*OFFSET_WIDTH)+4+(8*4));
   pipe_insert                <= pipe_OUT(pipe_width-4);
   pipe_insert_begin          <= pipe_OUT(pipe_width-3);
   pipe_eop_next_frame        <= pipe_OUT(pipe_width-2);
   pipe_EDIT_ENABLE           <= pipe_OUT(pipe_width-1);

   -- FLU_PIPE
   FLU_PIPE_inst :entity work.FLU_PIPE
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      FAKE_PIPE      => FAKE_PIPE,
      RESET_BY_INIT  => false,
      USE_OUTREG     => true
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      RX_DATA        => offset_DATA,
      RX_SOP_POS     => offset_SOP_POS,
      RX_EOP_POS     => offset_EOP_POS,
      RX_SOP         => offset_SOP,
      RX_EOP         => offset_EOP,
      RX_SRC_RDY     => offset_SRC_RDY,
      RX_DST_RDY     => offset_DST_RDY,

      TX_DATA        => pipe_DATA,
      TX_SOP_POS     => pipe_SOP_POS,
      TX_EOP_POS     => pipe_EOP_POS,
      TX_SOP         => pipe_SOP,
      TX_EOP         => pipe_EOP,
      TX_SRC_RDY     => pipe_SRC_RDY,
      TX_DST_RDY     => pipe_DST_RDY
   );

   INSERT_inst: entity work.INSERT
   generic map(
      DATA_WIDTH 	         => DATA_WIDTH,
      SOP_POS_WIDTH 	      => SOP_POS_WIDTH,
      OFFSET_WIDTH         => OFFSET_WIDTH
   )
   port map(
      CLK                  => CLK,
      RESET                => RESET,

      FLU_STATE            => pipe_flu_state,
      EOP_NEXT_FRAME       => pipe_eop_next_frame,
      BLOCK_INSER_OFFSET   => pipe_block_insert_offset,
      BLOCK_INSER_BEGIN    => pipe_insert_begin,
      RX_INSERT            => pipe_insert,
      RX_EDIT_ENABLE       => pipe_EDIT_ENABLE,
      RX_NEW_DATA          => pipe_NEW_DATA,
      RX_MASK              => pipe_MASK,
      RX_OFFSET            => pipe_offset,
      RX_DATA              => pipe_DATA,
      RX_SOP_POS           => pipe_SOP_POS,
      RX_EOP_POS           => pipe_EOP_POS,
      RX_SOP               => pipe_SOP,
      RX_EOP               => pipe_EOP,
      RX_SRC_RDY           => pipe_SRC_RDY,
      RX_DST_RDY           => pipe_DST_RDY,

      TX_EDIT_ENABLE       => TX_EDIT_ENABLE,
      TX_NEW_DATA          => TX_NEW_DATA,
      TX_MASK              => TX_MASK,
      TX_OFFSET            => TX_OFFSET,
      TX_DATA              => TX_DATA,
      TX_SOP_POS           => TX_SOP_POS,
      TX_EOP_POS           => TX_EOP_POS,
      TX_SOP               => TX_SOP,
      TX_EOP               => TX_EOP,
      TX_SRC_RDY           => TX_SRC_RDY,
      TX_DST_RDY           => TX_DST_RDY
   );

end architecture;

