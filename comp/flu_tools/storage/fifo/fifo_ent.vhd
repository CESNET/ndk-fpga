-- fifo_ent.vhd: Frame Link Unaliged protocol generic FIFO
-- Copyright (C) 2012 CESNET
-- Author: Lukas Kekely <kekely@cesnet.cz>
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
entity FLU_FIFO is
   generic(
      -- Data width
      -- Should be power of 2 and higher than 16
      DATA_WIDTH     : integer := 256;
      SOP_POS_WIDTH  : integer := 2;
      -- True => use BlockBAMs
      -- False => use SelectRAMs
      USE_BRAMS      : boolean := false;
      -- number of items in the FIFO
      ITEMS          : integer := 64;
      -- Size of block (for LSTBLK signal)
      BLOCK_SIZE     : integer := 1;
      -- Width of STATUS signal available
      STATUS_WIDTH   : integer := 1;
      -- Ouptut register
      OUTPUT_REG : boolean := true
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

       -- Frame Link Unaligned input interface
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      -- Frame Link Unaligned output interface
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic;

      -- FIFO state signals
      LSTBLK         : out std_logic;
      FULL           : out std_logic;
      EMPTY          : out std_logic;
      STATUS         : out std_logic_vector(STATUS_WIDTH-1 downto 0);
      FRAME_RDY      : out std_logic
   );
end entity FLU_FIFO;
