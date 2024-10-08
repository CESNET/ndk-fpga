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

entity PACKET_INSERT is
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

architecture full of PACKET_INSERT is
   constant offset_width_real : integer := OFFSET_WIDTH + 1;
   signal offset_real         : std_logic_vector(offset_width_real-1 downto 0);
   signal out_offset_real     : std_logic_vector(offset_width_real-1 downto 0);
begin
   offset_real(offset_width_real-1) <= '0';
   offset_real(offset_width_real-2 downto 0) <= RX_OFFSET;

   TX_OFFSET <= out_offset_real(offset_width_real-2 downto 0);

   INSERT_L_inst: entity work.PACKET_INSERT_L
   generic map(
      DATA_WIDTH        => DATA_WIDTH,
      SOP_POS_WIDTH     => SOP_POS_WIDTH,
      OFFSET_WIDTH      => offset_width_real,
      FAKE_PIPE         => FAKE_PIPE
   )
   port map(
      CLK               => CLK,
      RESET             => RESET,
      RX_INSERT_ENABLE  => RX_INSERT_ENABLE,
      RX_EDIT_ENABLE    => RX_EDIT_ENABLE,
      RX_NEW_DATA       => RX_NEW_DATA,
      RX_MASK           => RX_MASK,
      RX_OFFSET         => offset_real,
      RX_DATA           => RX_DATA,
      RX_SOP_POS        => RX_SOP_POS,
      RX_EOP_POS        => RX_EOP_POS,
      RX_SOP            => RX_SOP,
      RX_EOP            => RX_EOP,
      RX_SRC_RDY        => RX_SRC_RDY,
      RX_DST_RDY        => RX_DST_RDY,
      TX_EDIT_ENABLE    => TX_EDIT_ENABLE,
      TX_NEW_DATA       => TX_NEW_DATA,
      TX_MASK           => TX_MASK,
      TX_OFFSET         => out_offset_real,
      TX_DATA           => TX_DATA,
      TX_SOP_POS        => TX_SOP_POS,
      TX_EOP_POS        => TX_EOP_POS,
      TX_SOP            => TX_SOP,
      TX_EOP            => TX_EOP,
      TX_SRC_RDY        => TX_SRC_RDY,
      TX_DST_RDY        => TX_DST_RDY
   );
end architecture;

