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

entity MAC_EDITOR is
   generic(
      --! data width
      DATA_WIDTH 	   : integer := 512;
      --! sop_pos whidth (max value = log2(DATA_WIDTH/8))
      SOP_POS_WIDTH 	: integer := 3;
      FAKE_PIPE      : boolean := true
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      --! Data for destination MAC address
      DST_W          : in  std_logic;
      DST_DATA       : in  std_logic_vector(6*8-1 downto 0);
      DST_MASK       : in  std_logic_vector(6-1 downto 0);

      --! Data for source MAC address
      SRC_W          : in  std_logic;
      SRC_DATA       : in  std_logic_vector(6*8-1 downto 0);
      SRC_MASK       : in  std_logic_vector(6-1 downto 0);

      --! Frame Link Unaligned input interface
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS     : in  std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS     : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP         : in  std_logic;
      RX_EOP         : in  std_logic;
      RX_SRC_RDY     : in  std_logic;
      RX_DST_RDY     : out std_logic;

      --! Frame Link Unaligned output interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS     : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS     : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP         : out std_logic;
      TX_EOP         : out std_logic;
      TX_SRC_RDY     : out std_logic;
      TX_DST_RDY     : in  std_logic
   );
end entity;

