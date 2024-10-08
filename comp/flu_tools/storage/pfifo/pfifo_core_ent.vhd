-- pfifo_core_ent.vhd: Frame Link Unaliged protocol generic Packet Store-And-Forwad FIFO core
-- Copyright (C) 2012 CESNET
-- Author: Pavel Benacek <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FLU_PFIFO_CORE is
   generic(
      --! Data width
      --! \brief Should be power of 2 and higher than 16
      DATA_WIDTH     : integer := 256;
      SOP_POS_WIDTH  : integer := 2;
      --! number of items in the FIFO
      DFIFO_ITEMS   : integer := 64;
      --! Size of block (for LSTBLK signal)
      BLOCK_SIZE     : integer := 1;
      --! Width of STATUS signal available
      STATUS_WIDTH   : integer := 1
   );
   port(
      -----------------------------------------------------
      --! \name Clocking & Reset interface
      -----------------------------------------------------
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -----------------------------------------------------
      --! \name Frame Link Unaligned input interface
      -----------------------------------------------------
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;
      RX_STATUS     : out std_logic_vector(STATUS_WIDTH-1 downto 0);

      -----------------------------------------------------
      --! \name Frame Link Unaligned output interface
      -----------------------------------------------------
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic;

      -----------------------------------------------------
      --! \name Output statistical interface
      -----------------------------------------------------
      PACKET_COUNT   : out std_logic_vector(log2(DFIFO_ITEMS+1)-1 downto 0)

   );
end entity FLU_PFIFO_CORE;
