--
-- Copyright (C) 2014 CESNET
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

entity PACKET_INSERT_EDITOR is
   generic(
      --! data width
      DATA_WIDTH 	   : integer := 512;
      --! sop_pos whidth (max value = log2(DATA_WIDTH/8))
      SOP_POS_WIDTH 	: integer := 3;
      --! offset width (max 45 bits)
      --! select four bytes block of packet
      OFFSET_WIDTH   : integer := 10;
      --! enable input registers
      INPUT_PIPE     : boolean := true;
      --! enable mask
      EN_MASK        : boolean := true
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      --! offset of block (block = 4 bytes) in packet
      OFFSET         : in std_logic_vector(OFFSET_WIDTH-1 downto 0);
      --! enable insert data
      EN_INSERT      : in std_logic;
      --! enable replace data
      EN_REPLACE     : in std_logic;
      --! new bytes
      NEW_DATA       : in std_logic_vector(8*4-1 downto 0);
      --! mask bytes in NEW_DATA
      MASK           : in std_logic_vector(3 downto 0);

      --! Frame Link Unaligned input interface
      RX_DATA        : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS     : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS     : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP         : in std_logic;
      RX_EOP         : in std_logic;
      RX_SRC_RDY     : in std_logic;
      RX_DST_RDY     : out std_logic;

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

