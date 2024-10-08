-- pfifo_ent.vhd: Frame Link protocol generic packet FIFO
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
entity FL_PFIFO is
   generic(
      -- Data width
      -- Should be multiple of 16: only 16,32,64,128 supported
      DATA_WIDTH     : integer;
      -- number of items in the FIFO
      ITEMS          : integer;
      -- Size of block (for LSTBLK signal)
      BLOCK_SIZE     : integer;
      -- Width of STATUS signal available
      STATUS_WIDTH   : integer;
      -- Maximal number of packets
      MAX_DISCARD_BLOCKS : integer;
      -- Number of parts in each frame
      PARTS          : integer
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ====================
      -- write interface
      -- ====================

      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;

      -- ====================
      -- read interface
      -- ====================

      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;

      -- ====================
      -- FIFO control signals
      -- ====================

      -- drop current frame
      DISCARD        : in  std_logic;
      LSTBLK         : out std_logic;
      FULL           : out std_logic;
      EMPTY          : out std_logic;
      STATUS         : out std_logic_vector(STATUS_WIDTH-1 downto 0);
      FRAME_RDY      : out std_logic
   );
end entity FL_PFIFO;
