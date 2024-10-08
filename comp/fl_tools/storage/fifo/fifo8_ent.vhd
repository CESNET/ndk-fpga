-- fifo8_ent.vhd: 8 bit Frame Link protocol generic FIFO
-- Copyright (C) 2007 CESNET
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
entity FL_FIFO8 is
   generic(
      -- True => use BlockBAMs
      -- False => use SelectRAMs
      USE_BRAMS      : boolean;
      -- number of items in the FIFO
      ITEMS          : integer;
      -- Size of block (for LSTBLK signal)
      BLOCK_SIZE     : integer;
      -- Width of STATUS signal available
      STATUS_WIDTH   : integer;
      -- Number of parts in each frame
      PARTS          : integer;
      -- Ouptut register
      OUTPUT_REG : boolean := true
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- write interface
      RX_DATA        : in  std_logic_vector(8-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;

      -- read interface
      TX_DATA        : out std_logic_vector(8-1 downto 0);
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;

      -- FIFO state signals
      LSTBLK         : out std_logic;
      FULL           : out std_logic;
      EMPTY          : out std_logic;
      STATUS         : out std_logic_vector(STATUS_WIDTH-1 downto 0);
      FRAME_RDY      : out std_logic
   );
end entity FL_FIFO8;
